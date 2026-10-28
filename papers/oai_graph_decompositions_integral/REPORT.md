# Correctness report — oai_graph_decompositions_integral

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- Theorem 1.1: condition added (bookkeeping or a pinned reading)
- Corollary 2.2: condition added (bookkeeping or a pinned reading); ambiguous; a reading was pinned
- `r`: notation ambiguous; a reading was pinned
- `X`: notation ambiguous; a reading was pinned
- `\calD`: notation ambiguous; a reading was pinned
- `G`: notation ambiguous; a reading was pinned
- `p`: notation ambiguous; a reading was pinned
- `p_c`: notation ambiguous; a reading was pinned
- `S`: notation ambiguous; a reading was pinned
- `q`: notation ambiguous; a reading was pinned
- `H_i`: notation ambiguous; a reading was pinned
- `\mu_r`: notation ambiguous; a reading was pinned
- `\mathcal E_{K_0}(\calD)`: notation ambiguous; a reading was pinned
- `v`: notation ambiguous; a reading was pinned
- `d`: notation ambiguous; a reading was pinned
- `a`: notation ambiguous; a reading was pinned
- `m`: notation ambiguous; a reading was pinned
- `Y`: notation ambiguous; a reading was pinned
- `s`: notation ambiguous; a reading was pinned
- `\calR`: notation ambiguous; a reading was pinned
- `\calQ`: notation ambiguous; a reading was pinned
- `T`: notation ambiguous; a reading was pinned
- `G_*`: notation ambiguous; a reading was pinned
- `U`: notation ambiguous; a reading was pinned
- `N_J`: notation ambiguous; a reading was pinned
- `\Delta`: notation ambiguous; a reading was pinned
- `A`: notation ambiguous; a reading was pinned
- `C`: notation ambiguous; a reading was pinned
- `c`: notation ambiguous; a reading was pinned
- `t`: notation ambiguous; a reading was pinned
- `u`: notation ambiguous; a reading was pinned
- `q_J`: notation ambiguous; a reading was pinned
- `C_\ell`: notation ambiguous; a reading was pinned
- `u_\ell`: notation ambiguous; a reading was pinned

9 result(s) of the paper were examined. None was found wrong as printed. In Lean: 8 proved, 1 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**How a statement is read.**

- **Theorem 1.1.** The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat.

**Notation.**

- $r$: $r\in(0,1)$ is the product-measure parameter, also used as the source random-graph edge density. In Corollary~\ref{cor:typical-cover}: $q(H;n)<r<1$. In Proposition~\ref{prop:transfer}, Proposition~\ref{prop:degree-embedding}: $r$ and $s$ satisfy $s\in\mathbb N$, $s\leq10\log n$, and $r^s\geq n^{-1/100}$. In Theorem~\ref{thm:main}: In the large-degeneracy case of the proof, $r=2q(H;n)$.
- $X$: $X$ is a finite ground set. In Theorem~\ref{thm:main}, Corollary~\ref{cor:typical-cover}, Lemma~\ref{lem:q-lower}, Proposition~\ref{prop:stars}: For graph-containment covers, $X=E(K_n)$. In Theorem~\ref{thm:discrete}: $X$ is any nonempty finite set.
- $\calD$: $\calD\subseteq2^X$ is a fixed family of subsets of a finite ground set $X$ with $\mu_r(\calD)\geq1-1/K_0$. In Corollary~\ref{cor:typical-cover}: $X=E(K_n)$, and $\calD$ is any family of graphs on $[n]$ satisfying the stated mass bound; it need not be the particular family defined by source tests. In Proposition~\ref{prop:transfer}, \cite[Hall's theorem]{Hall35}, used in the proof of Proposition~\ref{prop:transfer}, Theorem~\ref{thm:main}: $X=E(K_n)$ and $\calD=\calD(n,r,s)$ consists of exactly those graphs $G$ for which, for every $Y\subseteq[n]$ with $|Y|\leq n^{2/3}$ and every nonempty $\calQ\subseteq\{T\subseteq Y:1\leq|T|\leq s\}$ with $|\calQ|\leq\lceil2r^{-s}\rceil$, one has $\frac{1}{n-|Y|}\sum_{w\in[n]\setminus Y}f_{\calQ}(N_G(w)\cap Y)\leq2x(\calQ)$. Here $x(\calQ)$ is the probability that a Bernoulli-$\tau$ subset of $Y$ satisfies $\calQ$, with $\tau=1-(1-r)^2$. In Theorem~\ref{thm:main}: In the large-degeneracy case, the chosen family uses $r=2q(H;n)$ and $s=\lceil2d/M\rceil$, where $d=\degen(H)$ and $M=1000$.
- $G$: $G$ denotes a labelled graph on $[n]$, identified with its edge set in $2^{E(K_n)}$. In Proposition~\ref{prop:transfer}, \cite[Hall's theorem]{Hall35}, used in the proof of Proposition~\ref{prop:transfer}: In the containment configuration and the Hall argument, $G$ is a fixed witness with $G\in\calD$ and $E(J)\subseteq E(G)$.
- $p$: $p\in[0,1]$ is the parameter used for edge inclusion and for evaluating cover cost. In Lemma~\ref{lem:q-lower}: In the proof of the second bound, $p=2^{-1/a}n^{-v/a}\in(0,1)$, where the chosen subgraph has $v$ vertices and $a\geq dv/2$ edges. In Proposition~\ref{prop:stars}: In the remaining nontrivial case of the proof, $q_J=q(J;n)>0$, $q_J<1/(2A)$, and $p=Aq_J\in(0,1/2)$, with $A=400e^4$.
- $p_c$: $p_c(J;n)$ is the containment threshold for a finite simple graph $J$ on at most $n$ vertices, with copies not required to be induced and with $p_c(J;n)=0$ for edgeless $J$.
- $S$: $S$ denotes a subset of the ground set in the covering relation, cost sum, or satisfaction test where it occurs. In Lemma~\ref{lem:compression}, Proposition~\ref{prop:transfer}: As an argument of satisfaction or $f_{\calQ}$, $S\subseteq Y$; $S$ satisfies $\calQ$ exactly when it contains some member of $\calQ$.
- $q$: $q(H;n)$ is the integral expectation threshold defined by the cover-cost maximum for graphs $H$ with $|V(H)|\leq n$, with $q(H;n)=0$ when $H$ is edgeless. In Theorem~\ref{thm:main}: After the edgeless case, the bare symbol $q$ abbreviates $q(H;n)>0$; in the subsequent nontrivial branch, $q<1/(2A)$.
- $H_i$: For $1\leq i\leq k$, $H_i$ is a possibly empty edge piece of $H$ in the partition $E(H)=E(H_1)\,\dot\cup\,\cdots\,\dot\cup\,E(H_k)$; the pieces may share vertices, and their separate embeddings need not agree on shared vertices.
- $\mu_r$: $\mu_r$ denotes the product law on subsets of the finite ground set in use, with each element included independently with probability $r$. In Corollary~\ref{cor:typical-cover}, Proposition~\ref{prop:transfer}: For a family $\calD$ of graphs on $[n]$, $\mu_r(\calD)$ is evaluated on the ground set $E(K_n)$. In Lemma~\ref{lem:compression}, Proposition~\ref{prop:transfer}, \cite[Hoeffding's inequality]{Hoeffding63}, used in the proof of Proposition~\ref{prop:transfer}: In the definition of $f_{\calQ}$, the ground set for $Z\sim\mu_r$ is $Y$.
- $\mathcal E_{K_0}(\calD)$: $\mathcal E_{K_0}(\calD)=\{S\subseteq X:S\not\subseteq D_1\cup\cdots\cup D_{K_0}\text{ for every }(D_1,\ldots,D_{K_0})\in\calD^{K_0}\}$, where tuple entries may repeat and $\calD$ need not be monotone.
- $v$: $v$ is locally bound, denoting either a vertex of the graph under discussion or the number of vertices of a locally chosen subgraph. In Lemma~\ref{lem:q-lower}: In the proof of the second bound, $v$ is the number of vertices of the chosen subgraph of $H$ of minimum degree $d$, whose edge count is $a\geq dv/2$; in particular, $1\leq v\leq n$.
- $d$: $d$ is a nonnegative integer degeneracy parameter. In Theorem~\ref{thm:main}, Lemma~\ref{lem:q-lower}: For $H$ having an edge, $d=\degen(H)\geq1$. In Lemma~\ref{lem:split}: The input graph has degeneracy at most $d$; equality is not required.
- $a$: $a$ is a locally bound integer whose different occurrences in separate proofs have independent meanings. In Lemma~\ref{lem:q-lower}: $a$ is the number of edges of the chosen subgraph of minimum degree $d$, with $v$ vertices, so $a\geq dv/2$ and $a\geq1$. In Proposition~\ref{prop:transfer}: $a\in[n]\setminus Y$ is a candidate image for an outside vertex $w$, usable when $N_J(w)\subseteq N_{G_*}(a)\cap Y$. In Theorem~\ref{thm:main}: $a=|Y\setminus Y_0|$ counts the vertices added to $Y_0$ during the closure procedure.
- $m$: $m$ is a locally specified positive integer. In Lemma~\ref{lem:split}: $m$ is any positive integer specifying the number of graphs in the edge partition. In Proposition~\ref{prop:transfer}: For each test set $Y$, $m=n-|Y|$ is the number of vertices outside $Y$. In Proposition~\ref{prop:stars}: For an integer $\ell\geq1$ with $m_\ell>0$, $m=m_\ell$ is the number of components with exactly $\ell$ leaves. In Theorem~\ref{thm:main}: In the applications of degeneracy splitting, $m=M=1000$.
- $Y$: $Y$ is a finite set on which the requirement subsets and their satisfaction tests are defined. In Theorem~\ref{thm:main}: In the large-degeneracy construction, start with $Y_0=\{v\in V(H):\deg_H(v)>\sqrt n\}$ and repeatedly add an outside vertex with more than $2d$ neighbors in the current set until none remains; $Y$ is the resulting set. It satisfies $|Y|\leq4d\sqrt n\leq n^{2/3}$, and every $w\notin Y$ has $\deg_H(w)\leq\sqrt n$ and $|N_H(w)\cap Y|\leq2d$. In Proposition~\ref{prop:transfer}, \cite[Hoeffding's inequality]{Hoeffding63}, used in the proof of Proposition~\ref{prop:transfer}, \cite[Hall's theorem]{Hall35}, used in the proof of Proposition~\ref{prop:transfer}: $Y\subseteq[n]$ with $|Y|\leq n^{2/3}$ is the part held fixed, and candidate images for vertices outside it are restricted to $[n]\setminus Y$.
- $s$: $s$ is an integer size bound for requirements or neighborhoods, with its value and additional restrictions specified locally. In Lemma~\ref{lem:compression}: $s\geq1$ is an integer and every $T\in\calR$ satisfies $1\leq|T|\leq s$. In Proposition~\ref{prop:transfer}, Proposition~\ref{prop:degree-embedding}, \cite[Hoeffding's inequality]{Hoeffding63}, used in the proof of Proposition~\ref{prop:transfer}, \cite[Hall's theorem]{Hall35}, used in the proof of Proposition~\ref{prop:transfer}: $s\in\mathbb N$, $s\leq10\log n$, and $r^s\geq n^{-1/100}$, with $0<r<1$. In Proposition~\ref{prop:transfer}: $s$ bounds the positive degrees in $J$ of vertices outside $Y$. In Proposition~\ref{prop:degree-embedding}: $s$ bounds $\degen(J)$. In Theorem~\ref{thm:main}: In the branch $d\geq M$, set $r=2q$ and $s=\lceil2d/M\rceil$, where $d=\degen(H)$ and $M=1000$.
- $\calR$: $\calR$ is a nonempty family of subsets of $Y$, each of size between $1$ and $s$. In Proposition~\ref{prop:transfer}: For a nonempty set $U$ of vertices to be matched, $\calR=\{N_J(w):w\in U\}$, with repeated neighborhoods represented only once.
- $\calQ$: $\calQ\subseteq2^Y$ is a family of requirements, and a set $S\subseteq Y$ satisfies it exactly when some $T\in\calQ$ is contained in $S$. In Lemma~\ref{lem:compression}: The asserted $\calQ$ is a nonempty subfamily of $\calR\subseteq\{T\subseteq Y:1\leq|T|\leq s\}$ with $|\calQ|\leq\lceil2r^{-s}\rceil$, such that every $S$ satisfying $\calR$ has $f_{\calQ}(S)\geq1/2$. During its construction the proof also uses $\calQ$ for the growing family initialized at $\varnothing$. In Proposition~\ref{prop:transfer}, \cite[Hoeffding's inequality]{Hoeffding63}, used in the proof of Proposition~\ref{prop:transfer}: The simultaneous tests range over every nonempty $\calQ\subseteq\{T\subseteq Y:1\leq|T|\leq s\}$ with $|\calQ|\leq\lceil2r^{-s}\rceil$. In Proposition~\ref{prop:transfer}: For a Hall test $U$, choose $\calQ\subseteq\calR=\{N_J(w):w\in U\}$ by compression; this choice may depend on $J,U,G$, since the source and target inequalities hold simultaneously for every admissible test.
- $T$: $T$ is local notation whose domain and meaning are determined by its occurrence. In Lemma~\ref{lem:compression}: $T\subseteq Y$ is a requirement set with $1\leq|T|\leq s$; in the selection procedure and its termination argument, $T\in\calR$. In Proposition~\ref{prop:transfer}: $T$ is a subset of $Y$ with $1\leq|T|\leq s$, indexing the allowed members of a test family. In Proposition~\ref{prop:stars}: $T$ is the random total number of center trials needed to finish all stars after infinitely many auxiliary centers with fresh independent rows have been appended; trials include failures.
- $G_*$: $G_*$ denotes the target graph on $[n]$ at density $r_*$. In Proposition~\ref{prop:transfer}: The target-event probability is evaluated under $G_*\sim G(n,r_*)$. In the Hall argument, $G_*$ is any fixed realization satisfying \eqref{eq:target-test} for every admissible test, and $Y$ is kept fixed during the embedding.
- $U$: $U$ indexes vertices to be matched to distinct candidate images. In Proposition~\ref{prop:transfer}: $U$ is any nonempty subset of the positive-degree vertices of $J$ in $[n]\setminus Y$, and its requirements are $\calR=\{N_J(w):w\in U\}$. In Proposition~\ref{prop:degree-embedding}: $U$ is any nonempty subset of the current layer, with $|U|=u$; its requirements are adjacency to the already embedded neighbors in earlier layers, and its candidate images lie in the current bin.
- $N_J$: $N_J(w)=\{v\in V(J):\{v,w\}\in E(J)\}$ for $w\in V(J)$. In Proposition~\ref{prop:transfer}: For a positive-degree vertex $w\in[n]\setminus Y$ to be matched, $N_J(w)\subseteq Y$ and $1\leq|N_J(w)|\leq s$.
- $\Delta$: $\Delta(J)$ denotes the maximum degree of $J$. In Proposition~\ref{prop:degree-embedding}: The bare symbol $\Delta$ abbreviates $\Delta(J)$ for the graph being embedded, with $\Delta(J)\leq n^{2/3}$.
- $A$: $A$ is context-dependent notation for a member of the family being covered or for a positive absolute numerical constant. In Theorem~\ref{thm:discrete}, Corollary~\ref{cor:typical-cover}, Lemma~\ref{lem:q-lower}: In the covering definition, $A$ ranges over the family being covered and is a subset of its ground set. In Proposition~\ref{prop:stars}, Theorem~\ref{thm:main}: In numerical expressions, $A=400e^4$.
- $C$: $C$ denotes an unspecified positive absolute constant in the bound where it occurs; its occurrences do not specify a common numerical value.
- $c$: $c>0$ denotes an absolute constant independent of the varying parameters; different estimates may use different values of $c$.
- $t$: $t$ is the number of independent-set layers constructed in reverse order after isolated vertices are discarded: each selected layer has size at least $m'/(2(4s+1))$ in the current residual graph on $m'$ vertices, and every vertex has at most $4s$ neighbors in earlier layers.
- $u$: $u=|U|\geq1$ is the cardinality of the nonempty set being tested by Hall's criterion. In Proposition~\ref{prop:degree-embedding}: $1\leq u\leq$ the size of the current layer; the corresponding set $W$ consists of $u-1$ vertices of its bin.
- $q_J$: $q_J=q(J;n)$. In Proposition~\ref{prop:stars}: The abbreviation is introduced for $J$ with at least one edge, so $q_J>0$; in the remaining branch of the proof, $q_J<1/(2A)$ and $p=Aq_J$.
- $C_\ell$: $C_\ell=n^{m(\ell+1)}/((\ell!)^m m!)$ is defined for integers $\ell\geq1$ with $m=m_\ell>0$ and bounds the number of copies on $[n]$ of $m$ disjoint $\ell$-edge stars.
- $u_\ell$: $u_\ell=\Prob(\Bin(b',p)\geq\ell)$ is a binomial-tail lower bound on the success probability of each trial for an $\ell$-leaf star conditional on the past.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean, given 1 cited result(s), under 1 condition(s) made explicit | `Papers.OaiGraphDecompositionsIntegral.main` (`TMain.lean:34`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Theorem 2.1 | taken from the literature as cited; not proved here | — | — |
| Corollary 2.2 | proved in Lean, given 1 cited result(s), under 1 condition(s) made explicit | `Papers.OaiGraphDecompositionsIntegral.typical_cover` (`TTypicalCover.lean:20`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.3 | proved in Lean | `Papers.OaiGraphDecompositionsIntegral.q_lower` (`Helpers/QLower.lean:247`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.4 | proved in Lean | `Papers.OaiGraphDecompositionsIntegral.degeneracy_split` (`Helpers/Degeneracy.lean:212`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.1 | proved in Lean | `Papers.OaiGraphDecompositionsIntegral.compression` (`Helpers/Compression.lean:160`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 3.2 | proved in Lean | `Papers.OaiGraphDecompositionsIntegral.transfer` (`TTransfer.lean:24`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 4.1 | proved in Lean | `Papers.OaiGraphDecompositionsIntegral.degree_embedding` (`TDegreeEmbedding.lean:25`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 4.2 | proved in Lean | `Papers.OaiGraphDecompositionsIntegral.stars` (`TStars.lean:56`) | the standard ones only (propext, Classical.choice, Quot.sound) |

**Taken from the literature, not proved here.**

- OpenAI26DC, Theorem 1.1 — checked against source supplied by the user at discovery/cited_sources/OpenAI26DC.txt

  What Lean assumes for it: `Papers.OaiGraphDecompositionsIntegral.DiscreteConvexityCover` (`Basic.lean:249`)

  ```lean
  def DiscreteConvexityCover : Sort 0 :=
    ∀ (X : Type) [Fintype X] [DecidableEq X] (r : ℝ) (D : Set (Finset X)),
      DiscreteGround X → DiscreteDensity r → DiscreteMass X r D →
      HasCoverOfCostLe (exceptionalFamily K0 D) r (1 / 2)
  ```

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (14 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `1a04312c8cd45d357e4b955277ff03cad68c768cc8b7e0f462c4985cf54583ac`)
- stage completed: `5`
- results in scope: 9

| bucket | count |
| --- | --- |
| verified | 6 |
| verified_with_bookkeeping | 0 |
| conditional | 3 |
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
| bucket | `conditional` |
| source | `main.tex:80-91` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} There exist an absolute integer $k\geq2$ and an absolute constant $L\geq1$ such that, for every $n\geq2$ and every graph $H$ on at most $n$ vertices, the edges of $H$ admit a partition \[ E(H)=E(H_1)\,\dot\cup\,\cdots\,\dot\cup\,E(H_k) \quad\text{with}\quad p_c(H_i;n)\leq Lq(H;n)\qquad(1\leq i\leq k). \] The pieces may be empty and may share vertices. The partition depends only on $H,n$ and is fixed before the random host is sampled. |
| Lean | `TMain.lean:34` — `Papers.OaiGraphDecompositionsIntegral.main` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | `thm:discrete` (OpenAI26DC, Theorem 1.1) |
| assumed substrate gates | — |
| findings | — |

### 2. Discrete convexity, {\cite[Theorem~1.1]{OpenAI26DC}} `thm:discrete`

| field | value |
| --- | --- |
| bucket | `conditional` |
| source | `main.tex:185-198` (`theorem`, label `thm:discrete`) |
| statement | \label{thm:discrete} Set $K_0=2^{75}$. For every nonempty finite set $X$, every $r\in(0,1)$, and every family $\calD\subseteq2^X$ with $\mu_r(\calD)\geq1-1/K_0$, the family \[ \mathcal E_{K_0}(\calD)= \{S\subseteq X:S\not\subseteq D_1\cup\cdots\cup D_{K_0} \text{ for every }D_1,\ldots,D_{K_0}\in\calD\} \] has a cover of cost at most $1/2$ at the same parameter $r$. The family $\calD$ need not be monotone, and members of a tuple may repeat. |
| Lean | no declaration anchored |
| crosswalk verdict | — |
| axioms | — |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | `thm:discrete` (OpenAI26DC, Theorem 1.1) |
| assumed substrate gates | — |
| findings | [note, V1.5] cited source checked: source supplied by the user at discovery/cited_sources/OpenAI26DC.txt |

### 3. cor:typical-cover `thm:typical-cover`

| field | value |
| --- | --- |
| bucket | `conditional` |
| source | `main.tex:200-205` (`corollary`, label `cor:typical-cover`) |
| statement | \label{cor:typical-cover} Let $n\geq2$, let $H$ have an edge and at most $n$ vertices, and suppose $q(H;n)<r<1$. If a family of graphs on $[n]$ satisfies $\mu_r(\calD)\geq1-1/K_0$, then some copy of $H$ has its edges contained in the union of $K_0$ members of $\calD$. |
| Lean | `TTypicalCover.lean:20` — `Papers.OaiGraphDecompositionsIntegral.typical_cover` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity pinned · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | `thm:discrete` (OpenAI26DC, Theorem 1.1) |
| assumed substrate gates | — |
| findings | [note, V1.5] pinned reading: The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat. (Theorem~\ref{thm:discrete} explicitly allows repeated tuple members, and Corollary~\ref{cor:typical-cover} uses precisely that theorem and its exceptional family.) |

### 4. `lem:q-lower`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:238-244` (`lemma`, label `lem:q-lower`) |
| statement | \label{lem:q-lower} If $H$ has an edge, $\|V(H)\|\leq n$, and $d=\degen(H)$, then \begin{equation}\label{eq:q-lower} q(H;n)\geq\frac1{2\binom n2},\qquad q(H;n)\geq\frac12 n^{-2/d}. \end{equation} |
| Lean | `Helpers/QLower.lean:247` — `Papers.OaiGraphDecompositionsIntegral.q_lower` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. Degeneracy splitting `lem:split`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:258-262` (`lemma`, label `lem:split`) |
| statement | \label{lem:split} For every positive integer $m$, the edges of a $d$-degenerate graph can be partitioned into $m$ graphs, each of degeneracy at most $\lceil d/m\rceil$. |
| Lean | `Helpers/Degeneracy.lean:212` — `Papers.OaiGraphDecompositionsIntegral.degeneracy_split` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 6. Compression after a random extension `lem:compression`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:298-311` (`lemma`, label `lem:compression`) |
| statement | \label{lem:compression} Let $Y$ be finite, $r\in(0,1)$, and $s\geq1$ an integer. For every nonempty family \[ \calR\subseteq\{T\subseteq Y:1\leq\|T\|\leq s\} \] there is a nonempty subfamily $\calQ\subseteq\calR$ with $\|\calQ\|\leq\lceil2r^{-s}\rceil$ such that \begin{equation}\label{eq:compression} S\text{ satisfies }\calR\quad\Longrightarrow\quad f_{\calQ}(S)\geq1/2. \end{equation} |
| Lean | `Helpers/Compression.lean:160` — `Papers.OaiGraphDecompositionsIntegral.compression` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 7. Neighborhood transfer `prop:transfer`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:346-364` (`proposition`, label `prop:transfer`) |
| statement | \label{prop:transfer} There is an absolute integer $N_1$ such that the following holds for every $n\geq N_1$ and every $r,s$ satisfying \eqref{eq:parameters}. There exists $\calD=\calD(n,r,s)\subseteq2^{E(K_n)}$ with $\mu_r(\calD)\geq1-1/K_0$ such that, whenever \begin{itemize} \item $Y\subseteq[n]$ has $\|Y\|\leq n^{2/3}$; \item $J$ is a labelled bipartite graph with all edges between $Y$ and $[n]\setminus Y$, and $E(J)\subseteq E(G)$ for some $G\in\calD$; \item at most $n/8$ vertices outside $Y$ have positive degree in $J$, and all of those degrees are at most $s$; \end{itemize} one has \begin{equation}\label{eq:transfer} p_c(J;n)\leq r_*:=1-(1-r)^{32}\leq32r. \end{equation} |
| Lean | `TTransfer.lean:24` — `Papers.OaiGraphDecompositionsIntegral.transfer` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 8. `prop:degree-embedding`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:499-508` (`proposition`, label `prop:degree-embedding`) |
| statement | \label{prop:degree-embedding} There is an absolute integer $N_2$ such that, for $n\geq N_2$ and $r,s$ satisfying \eqref{eq:parameters}, every graph $J$ with \[ \|V_+(J)\|\leq n/4,\qquad \degen(J)\leq s, \qquad\Delta(J)\leq n^{2/3} \] and at most $n$ vertices satisfies $p_c(J;n)\leq r$. |
| Lean | `TDegreeEmbedding.lean:25` — `Papers.OaiGraphDecompositionsIntegral.degree_embedding` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 9. `prop:stars`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:587-596` (`proposition`, label `prop:stars`) |
| statement | \label{prop:stars} Put $A=400e^4$. There is an absolute integer $N_3$ such that, for every $n\geq N_3$ and every star forest $J$ on at most $n$ vertices with $\|V_+(J)\|\leq n/100$, \begin{equation}\label{eq:star-threshold} p_c(J;n)\leq2Aq(J;n). \end{equation} If $q(J;n)<1/(2A)$, the stronger bound $p_c(J;n)\leq Aq(J;n)$ holds. |
| Lean | `TStars.lean:56` — `Papers.OaiGraphDecompositionsIntegral.stars` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Corrected version

2 of 9 result(s) differ from the version you provided — 0 repaired, 0 with the proof completed (no error), 2 only with a side condition or reading made explicit; the others are as printed. The Lean formalization is of the corrected version.

### `thm:main` (`main.tex:80-91`)

- as printed: \label{thm:main} There exist an absolute integer $k\geq2$ and an absolute constant $L\geq1$ such that, for every $n\geq2$ and every graph $H$ on at most $n$ vertices, the edges of $H$ admit a partition \[ E(H)=E(H_1)\,\dot\cup\,\cdots\,\dot\cup\,E(H_k) \quad\text{with}\quad p_c(H_i;n)\leq Lq(H;n)\qquad(1\leq i\leq k). \] The pieces may be empty and may share vertices. The partition depends only on $H,n$ and is fixed before the random host is sampled.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat. — pins reading of thm:typical-cover: Theorem~\ref{thm:discrete} explicitly allows repeated tuple members, and Corollary~\ref{cor:typical-cover} uses precisely that theorem and its exceptional family.

### `thm:typical-cover` (`main.tex:200-205`)

- as printed: \label{cor:typical-cover} Let $n\geq2$, let $H$ have an edge and at most $n$ vertices, and suppose $q(H;n)<r<1$. If a family of graphs on $[n]$ satisfies $\mu_r(\calD)\geq1-1/K_0$, then some copy of $H$ has its edges contained in the union of $K_0$ members of $\calD$.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat. — pins reading of thm:typical-cover: Theorem~\ref{thm:discrete} explicitly allows repeated tuple members, and Corollary~\ref{cor:typical-cover} uses precisely that theorem and its exceptional family.

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- clarification (`ass:pin-1`, used by `thm:main`): The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat. — pins reading of thm:typical-cover: Theorem~\ref{thm:discrete} explicitly allows repeated tuple members, and Corollary~\ref{cor:typical-cover} uses precisely that theorem and its exceptional family.
- `thm:typical-cover`: pinned reading: The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat. (Theorem~\ref{thm:discrete} explicitly allows repeated tuple members, and Corollary~\ref{cor:typical-cover} uses precisely that theorem and its exceptional family.)
- reading of the symbol `r`: $r\in(0,1)$ is the product-measure parameter, also used as the source random-graph edge density. In Corollary~\ref{cor:typical-cover}: $q(H;n)<r<1$. In Proposition~\ref{prop:transfer}, Proposition~\ref{prop:degree-embedding}: $r$ and $s$ satisfy $s\in\mathbb N$, $s\leq10\log n$, and $r^s\geq n^{-1/100}$. In Theorem~\ref{thm:main}: In the large-degeneracy case of the proof, $r=2q(H;n)$. — The product-measure definition, the hypotheses of Corollary~\ref{cor:typical-cover}, equation~\eqref{eq:parameters}, and the large-degeneracy part of the proof of Theorem~\ref{thm:main} specify these ranges and choices.
- reading of the symbol `X`: $X$ is a finite ground set. In Theorem~\ref{thm:main}, Corollary~\ref{cor:typical-cover}, Lemma~\ref{lem:q-lower}, Proposition~\ref{prop:stars}: For graph-containment covers, $X=E(K_n)$. In Theorem~\ref{thm:discrete}: $X$ is any nonempty finite set. — The introduction sets $X=E(K_n)$ for graph containment; Section~\ref{sec:prelim} explicitly extends the notation to a finite ground set, and Theorem~\ref{thm:discrete} requires it to be nonempty.
- reading of the symbol `\calD`: $\calD\subseteq2^X$ is a fixed family of subsets of a finite ground set $X$ with $\mu_r(\calD)\geq1-1/K_0$. In Corollary~\ref{cor:typical-cover}: $X=E(K_n)$, and $\calD$ is any family of graphs on $[n]$ satisfying the stated mass bound; it need not be the particular family defined by source tests. In Proposition~\ref{prop:transfer}, \cite[Hall's theorem]{Hall35}, used in the proof of Proposition~\ref{prop:transfer}, Theorem~\ref{thm:main}: $X=E(K_n)$ and $\calD=\calD(n,r,s)$ consists of exactly those graphs $G$ for which, for every $Y\subseteq[n]$ with $\|Y\|\leq n^{2/3}$ and every nonempty $\calQ\subseteq\{T\subseteq Y:1\leq\|T\|\leq s\}$ with $\|\calQ\|\leq\lceil2r^{-s}\rceil$, one has $\frac{1}{n-\|Y\|}\sum_{w\in[n]\setminus Y}f_{\calQ}(N_G(w)\cap Y)\leq2x(\calQ)$. Here $x(\calQ)$ is the probability that a Bernoulli-$\tau$ subset of $Y$ satisfies $\calQ$, with $\tau=1-(1-r)^2$. In Theorem~\ref{thm:main}: In the large-degeneracy case, the chosen family uses $r=2q(H;n)$ and $s=\lceil2d/M\rceil$, where $d=\degen(H)$ and $M=1000$. — Theorem~\ref{thm:discrete} quantifies over arbitrary such families and explicitly allows nonmonotone families. Corollary~\ref{cor:typical-cover} specializes to graphs on $[n]$. The proof of Proposition~\ref{prop:transfer} defines its particular family by all source tests simultaneously, and the proof of Theorem~\ref{thm:main} takes that family.
- reading of the symbol `G`: $G$ denotes a labelled graph on $[n]$, identified with its edge set in $2^{E(K_n)}$. In Proposition~\ref{prop:transfer}, \cite[Hall's theorem]{Hall35}, used in the proof of Proposition~\ref{prop:transfer}: In the containment configuration and the Hall argument, $G$ is a fixed witness with $G\in\calD$ and $E(J)\subseteq E(G)$. — Proposition~\ref{prop:transfer} requires a witness $G\in\calD$ containing the labelled edges of $J$. Its concentration argument instead evaluates the source tests for $G\sim G(n,r)$; the Hall argument then fixes $J,Y,G$ as in the statement.
- reading of the symbol `p`: $p\in[0,1]$ is the parameter used for edge inclusion and for evaluating cover cost. In Lemma~\ref{lem:q-lower}: In the proof of the second bound, $p=2^{-1/a}n^{-v/a}\in(0,1)$, where the chosen subgraph has $v$ vertices and $a\geq dv/2$ edges. In Proposition~\ref{prop:stars}: In the remaining nontrivial case of the proof, $q_J=q(J;n)>0$, $q_J<1/(2A)$, and $p=Aq_J\in(0,1/2)$, with $A=400e^4$. — The introduction defines the host and cover cost at parameter $p$. The proof of Lemma~\ref{lem:q-lower} explicitly chooses $p=2^{-1/a}n^{-v/a}$, and the remaining case in the proof of Proposition~\ref{prop:stars} sets $p=Aq_J\in(0,1/2)$.
- reading of the symbol `p_c`: $p_c(J;n)$ is the containment threshold for a finite simple graph $J$ on at most $n$ vertices, with copies not required to be induced and with $p_c(J;n)=0$ for edgeless $J$. — The opening paragraph of Section~\ref{sec:intro} specifies finite simple graphs, noninduced containment, the vertex bound, and the edgeless convention.
- reading of the symbol `S`: $S$ denotes a subset of the ground set in the covering relation, cost sum, or satisfaction test where it occurs. In Lemma~\ref{lem:compression}, Proposition~\ref{prop:transfer}: As an argument of satisfaction or $f_{\calQ}$, $S\subseteq Y$; $S$ satisfies $\calQ$ exactly when it contains some member of $\calQ$. — The introduction uses $S\in\mathcal C\subseteq2^X$; Theorem~\ref{thm:discrete} quantifies $S\subseteq X$; the satisfaction and smoothing definitions explicitly use $S\subseteq Y$.
- reading of the symbol `q`: $q(H;n)$ is the integral expectation threshold defined by the cover-cost maximum for graphs $H$ with $\|V(H)\|\leq n$, with $q(H;n)=0$ when $H$ is edgeless. In Theorem~\ref{thm:main}: After the edgeless case, the bare symbol $q$ abbreviates $q(H;n)>0$; in the subsequent nontrivial branch, $q<1/(2A)$. — The introduction defines the functional in equation~\ref{eq:q-definition}; the assembly proof explicitly introduces its scalar abbreviation after the edgeless case.
- reading of the symbol `H_i`: For $1\leq i\leq k$, $H_i$ is a possibly empty edge piece of $H$ in the partition $E(H)=E(H_1)\,\dot\cup\,\cdots\,\dot\cup\,E(H_k)$; the pieces may share vertices, and their separate embeddings need not agree on shared vertices. — Theorem~\ref{thm:main} specifies the index range, edge partition, and permission to share vertices; the abstract explicitly states that separate embeddings need not agree.
- reading of the symbol `\mu_r`: $\mu_r$ denotes the product law on subsets of the finite ground set in use, with each element included independently with probability $r$. In Corollary~\ref{cor:typical-cover}, Proposition~\ref{prop:transfer}: For a family $\calD$ of graphs on $[n]$, $\mu_r(\calD)$ is evaluated on the ground set $E(K_n)$. In Lemma~\ref{lem:compression}, Proposition~\ref{prop:transfer}, \cite[Hoeffding's inequality]{Hoeffding63}, used in the proof of Proposition~\ref{prop:transfer}: In the definition of $f_{\calQ}$, the ground set for $Z\sim\mu_r$ is $Y$. — The definition preceding Theorem~\ref{thm:discrete} uses an arbitrary finite ground set; Corollary~\ref{cor:typical-cover} and Proposition~\ref{prop:transfer} apply it to edge sets, while \eqref{eq:smoothed-test} explicitly uses it on $Y$.
- reading of the symbol `\mathcal E_{K_0}(\calD)`: $\mathcal E_{K_0}(\calD)=\{S\subseteq X:S\not\subseteq D_1\cup\cdots\cup D_{K_0}\text{ for every }(D_1,\ldots,D_{K_0})\in\calD^{K_0}\}$, where tuple entries may repeat and $\calD$ need not be monotone. — The defining display and final sentence of Theorem~\ref{thm:discrete} explicitly specify universal quantification over tuples, allow repetitions, and impose no monotonicity requirement.
- reading of the symbol `v`: $v$ is locally bound, denoting either a vertex of the graph under discussion or the number of vertices of a locally chosen subgraph. In Lemma~\ref{lem:q-lower}: In the proof of the second bound, $v$ is the number of vertices of the chosen subgraph of $H$ of minimum degree $d$, whose edge count is $a\geq dv/2$; in particular, $1\leq v\leq n$. — The definition of $V_+(J)$ binds $v\in V(J)$, and the definition of $Y_0$ binds $v\in V(H)$; the proof of Lemma~\ref{lem:q-lower} instead introduces a subgraph with $v$ vertices.
- reading of the symbol `d`: $d$ is a nonnegative integer degeneracy parameter. In Theorem~\ref{thm:main}, Lemma~\ref{lem:q-lower}: For $H$ having an edge, $d=\degen(H)\geq1$. In Lemma~\ref{lem:split}: The input graph has degeneracy at most $d$; equality is not required. — The degeneracy definition and Lemma~\ref{lem:q-lower} set $d=\degen(H)$; the proof of Theorem~\ref{thm:main} repeats this choice for nonempty $H$; Lemma~\ref{lem:split} assumes only a $d$-degenerate graph.
- reading of the symbol `a`: $a$ is a locally bound integer whose different occurrences in separate proofs have independent meanings. In Lemma~\ref{lem:q-lower}: $a$ is the number of edges of the chosen subgraph of minimum degree $d$, with $v$ vertices, so $a\geq dv/2$ and $a\geq1$. In Proposition~\ref{prop:transfer}: $a\in[n]\setminus Y$ is a candidate image for an outside vertex $w$, usable when $N_J(w)\subseteq N_{G_*}(a)\cap Y$. In Theorem~\ref{thm:main}: $a=\|Y\setminus Y_0\|$ counts the vertices added to $Y_0$ during the closure procedure. — The proof of Lemma~\ref{lem:q-lower} introduces an edge count; the proof of Proposition~\ref{prop:transfer} introduces a candidate image; the proof of Theorem~\ref{thm:main} defines an added-vertex count.
- reading of the symbol `m`: $m$ is a locally specified positive integer. In Lemma~\ref{lem:split}: $m$ is any positive integer specifying the number of graphs in the edge partition. In Proposition~\ref{prop:transfer}: For each test set $Y$, $m=n-\|Y\|$ is the number of vertices outside $Y$. In Proposition~\ref{prop:stars}: For an integer $\ell\geq1$ with $m_\ell>0$, $m=m_\ell$ is the number of components with exactly $\ell$ leaves. In Theorem~\ref{thm:main}: In the applications of degeneracy splitting, $m=M=1000$. — Lemma~\ref{lem:split} quantifies over positive integers $m$; the proof of Proposition~\ref{prop:transfer} writes $m=n-\|Y\|$; the proof of Proposition~\ref{prop:stars} sets $m=m_\ell>0$; the proof of Theorem~\ref{thm:main} applies splitting with $m=M$.
- reading of the symbol `Y`: $Y$ is a finite set on which the requirement subsets and their satisfaction tests are defined. In Theorem~\ref{thm:main}: In the large-degeneracy construction, start with $Y_0=\{v\in V(H):\deg_H(v)>\sqrt n\}$ and repeatedly add an outside vertex with more than $2d$ neighbors in the current set until none remains; $Y$ is the resulting set. It satisfies $\|Y\|\leq4d\sqrt n\leq n^{2/3}$, and every $w\notin Y$ has $\deg_H(w)\leq\sqrt n$ and $\|N_H(w)\cap Y\|\leq2d$. In Proposition~\ref{prop:transfer}, \cite[Hoeffding's inequality]{Hoeffding63}, used in the proof of Proposition~\ref{prop:transfer}, \cite[Hall's theorem]{Hall35}, used in the proof of Proposition~\ref{prop:transfer}: $Y\subseteq[n]$ with $\|Y\|\leq n^{2/3}$ is the part held fixed, and candidate images for vertices outside it are restricted to $[n]\setminus Y$. — The satisfaction definition and compression lemma allow any finite $Y$. The transfer statement restricts $Y$ to a small subset of $[n]$, and the assembly proof constructs it by enlarging $Y_0$.
- reading of the symbol `s`: $s$ is an integer size bound for requirements or neighborhoods, with its value and additional restrictions specified locally. In Lemma~\ref{lem:compression}: $s\geq1$ is an integer and every $T\in\calR$ satisfies $1\leq\|T\|\leq s$. In Proposition~\ref{prop:transfer}, Proposition~\ref{prop:degree-embedding}, \cite[Hoeffding's inequality]{Hoeffding63}, used in the proof of Proposition~\ref{prop:transfer}, \cite[Hall's theorem]{Hall35}, used in the proof of Proposition~\ref{prop:transfer}: $s\in\mathbb N$, $s\leq10\log n$, and $r^s\geq n^{-1/100}$, with $0<r<1$. In Proposition~\ref{prop:transfer}: $s$ bounds the positive degrees in $J$ of vertices outside $Y$. In Proposition~\ref{prop:degree-embedding}: $s$ bounds $\degen(J)$. In Theorem~\ref{thm:main}: In the branch $d\geq M$, set $r=2q$ and $s=\lceil2d/M\rceil$, where $d=\degen(H)$ and $M=1000$. — Lemma~\ref{lem:compression} assumes an integer $s\geq1$. Equation~\eqref{eq:parameters} specifies the uniform parameter range used in Propositions~\ref{prop:transfer} and~\ref{prop:degree-embedding}; their statements specify the degree bounds. The large-degeneracy branch of the proof of Theorem~\ref{thm:main} sets $s=\lceil2d/M\rceil$.
- reading of the symbol `\calR`: $\calR$ is a nonempty family of subsets of $Y$, each of size between $1$ and $s$. In Proposition~\ref{prop:transfer}: For a nonempty set $U$ of vertices to be matched, $\calR=\{N_J(w):w\in U\}$, with repeated neighborhoods represented only once. — Lemma~\ref{lem:compression} permits every such family. The proof of Proposition~\ref{prop:transfer} instantiates it by the displayed family of neighborhoods and explicitly notes that repeated neighborhoods disappear.
- reading of the symbol `\calQ`: $\calQ\subseteq2^Y$ is a family of requirements, and a set $S\subseteq Y$ satisfies it exactly when some $T\in\calQ$ is contained in $S$. In Lemma~\ref{lem:compression}: The asserted $\calQ$ is a nonempty subfamily of $\calR\subseteq\{T\subseteq Y:1\leq\|T\|\leq s\}$ with $\|\calQ\|\leq\lceil2r^{-s}\rceil$, such that every $S$ satisfying $\calR$ has $f_{\calQ}(S)\geq1/2$. During its construction the proof also uses $\calQ$ for the growing family initialized at $\varnothing$. In Proposition~\ref{prop:transfer}, \cite[Hoeffding's inequality]{Hoeffding63}, used in the proof of Proposition~\ref{prop:transfer}: The simultaneous tests range over every nonempty $\calQ\subseteq\{T\subseteq Y:1\leq\|T\|\leq s\}$ with $\|\calQ\|\leq\lceil2r^{-s}\rceil$. In Proposition~\ref{prop:transfer}: For a Hall test $U$, choose $\calQ\subseteq\calR=\{N_J(w):w\in U\}$ by compression; this choice may depend on $J,U,G$, since the source and target inequalities hold simultaneously for every admissible test. — The satisfaction definition gives the general meaning. The compression lemma specifies its selected subfamily, the test-family paragraph specifies the transfer tests, and the Hall argument selects a test from neighborhood requirements.
- reading of the symbol `T`: $T$ is local notation whose domain and meaning are determined by its occurrence. In Lemma~\ref{lem:compression}: $T\subseteq Y$ is a requirement set with $1\leq\|T\|\leq s$; in the selection procedure and its termination argument, $T\in\calR$. In Proposition~\ref{prop:transfer}: $T$ is a subset of $Y$ with $1\leq\|T\|\leq s$, indexing the allowed members of a test family. In Proposition~\ref{prop:stars}: $T$ is the random total number of center trials needed to finish all stars after infinitely many auxiliary centers with fresh independent rows have been appended; trials include failures. — Lemma~\ref{lem:compression} uses $T$ for requirement sets; the test families in Proposition~\ref{prop:transfer} use the same set notation. The proof of Proposition~\ref{prop:stars} introduces $T$ as the total number of trials in the enlarged process.
- reading of the symbol `G_*`: $G_*$ denotes the target graph on $[n]$ at density $r_*$. In Proposition~\ref{prop:transfer}: The target-event probability is evaluated under $G_*\sim G(n,r_*)$. In the Hall argument, $G_*$ is any fixed realization satisfying \eqref{eq:target-test} for every admissible test, and $Y$ is kept fixed during the embedding. — Concentration is evaluated for $G_*\sim G(n,r_*)$; the Hall paragraph then says to fix a target graph satisfying the simultaneous target inequalities.
- reading of the symbol `U`: $U$ indexes vertices to be matched to distinct candidate images. In Proposition~\ref{prop:transfer}: $U$ is any nonempty subset of the positive-degree vertices of $J$ in $[n]\setminus Y$, and its requirements are $\calR=\{N_J(w):w\in U\}$. In Proposition~\ref{prop:degree-embedding}: $U$ is any nonempty subset of the current layer, with $\|U\|=u$; its requirements are adjacency to the already embedded neighbors in earlier layers, and its candidate images lie in the current bin. — The transfer proof tests nonempty sets of positive-degree vertices outside $Y$; the degree-embedding proof instead fixes a subset of the current layer.
- reading of the symbol `N_J`: $N_J(w)=\{v\in V(J):\{v,w\}\in E(J)\}$ for $w\in V(J)$. In Proposition~\ref{prop:transfer}: For a positive-degree vertex $w\in[n]\setminus Y$ to be matched, $N_J(w)\subseteq Y$ and $1\leq\|N_J(w)\|\leq s$. — The transfer setup writes $T_w=N_J(w)\subseteq Y$; the proposition places all edges of $J$ between $Y$ and its complement and bounds the positive degrees outside $Y$ by $s$.
- reading of the symbol `\Delta`: $\Delta(J)$ denotes the maximum degree of $J$. In Proposition~\ref{prop:degree-embedding}: The bare symbol $\Delta$ abbreviates $\Delta(J)$ for the graph being embedded, with $\Delta(J)\leq n^{2/3}$. — The degree-embedding statement uses $\Delta(J)$, and its proof explicitly says, "Write $\Delta=\Delta(J)$."
- reading of the symbol `A`: $A$ is context-dependent notation for a member of the family being covered or for a positive absolute numerical constant. In Theorem~\ref{thm:discrete}, Corollary~\ref{cor:typical-cover}, Lemma~\ref{lem:q-lower}: In the covering definition, $A$ ranges over the family being covered and is a subset of its ground set. In Proposition~\ref{prop:stars}, Theorem~\ref{thm:main}: In numerical expressions, $A=400e^4$. — The introductory covering definition quantifies over $A\in\calF_H$, the preliminary section extends covering to a general finite ground set, and Proposition~\ref{prop:stars} specifies the numerical value subsequently used in the assembly proof.
- reading of the symbol `C`: $C$ denotes an unspecified positive absolute constant in the bound where it occurs; its occurrences do not specify a common numerical value. — The introductory logarithmic comparison and equation~\eqref{eq:test-count} each introduce an absolute $C$; equation~\eqref{eq:uniform-error} uses the test-count bound.
- reading of the symbol `c`: $c>0$ denotes an absolute constant independent of the varying parameters; different estimates may use different values of $c$. — The concentration argument explicitly says "with another absolute $c>0$"; the later Hall-exponent estimate also uses an absolute positive constant.
- reading of the symbol `t`: $t$ is the number of independent-set layers constructed in reverse order after isolated vertices are discarded: each selected layer has size at least $m'/(2(4s+1))$ in the current residual graph on $m'$ vertices, and every vertex has at most $4s$ neighbors in earlier layers. — The layer construction preceding equation~\eqref{eq:layers} specifies both the selection rule and the earlier-neighbor property.
- reading of the symbol `u`: $u=\|U\|\geq1$ is the cardinality of the nonempty set being tested by Hall's criterion. In Proposition~\ref{prop:degree-embedding}: $1\leq u\leq$ the size of the current layer; the corresponding set $W$ consists of $u-1$ vertices of its bin. — The proof writes: "Fix a subset $U$ of the current layer with $\|U\|=u\geq1$."
- reading of the symbol `q_J`: $q_J=q(J;n)$. In Proposition~\ref{prop:stars}: The abbreviation is introduced for $J$ with at least one edge, so $q_J>0$; in the remaining branch of the proof, $q_J<1/(2A)$ and $p=Aq_J$. — The star-forest proof introduces the abbreviation after disposing of the edgeless case and subsequently restricts the remaining branch.
- reading of the symbol `C_\ell`: $C_\ell=n^{m(\ell+1)}/((\ell!)^m m!)$ is defined for integers $\ell\geq1$ with $m=m_\ell>0$ and bounds the number of copies on $[n]$ of $m$ disjoint $\ell$-edge stars. — The definition follows the restriction "If $m=m_\ell>0$" and the preceding introduction "For $\ell\geq1$".
- reading of the symbol `u_\ell`: $u_\ell=\Prob(\Bin(b',p)\geq\ell)$ is a binomial-tail lower bound on the success probability of each trial for an $\ell$-leaf star conditional on the past. — The paragraph preceding equation~\eqref{eq:star-success} explicitly states the conditional lower bound, and equation~\eqref{eq:expected-trials} uses it to bound waiting times.

## Added conditions

| id | where | class | condition |
| --- | --- | --- | --- |
| `ass:pin-1` | `thm:main` | V1.5 bookkeeping | The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat. (pins reading of thm:typical-cover: Theorem~\ref{thm:discrete} explicitly allows repeated tuple members, and Corollary~\ref{cor:typical-cover} uses precisely that theorem and its exceptional family.) |
| `ass:pin-1` | `thm:typical-cover` | V1.5 bookkeeping | The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat. (pins reading of thm:typical-cover: Theorem~\ref{thm:discrete} explicitly allows repeated tuple members, and Corollary~\ref{cor:typical-cover} uses precisely that theorem and its exceptional family.) |

## Conditions assumed

### Cited results

| id | used by | citation | locator | checked against |
| --- | --- | --- | --- | --- |
| `thm:discrete` | `thm:main` | OpenAI26DC | Theorem 1.1 | source supplied by the user at discovery/cited_sources/OpenAI26DC.txt |
| `thm:discrete` | `thm:discrete` | OpenAI26DC | Theorem 1.1 | source supplied by the user at discovery/cited_sources/OpenAI26DC.txt |
| `thm:discrete` | `thm:typical-cover` | OpenAI26DC | Theorem 1.1 | source supplied by the user at discovery/cited_sources/OpenAI26DC.txt |

`thm:discrete` (OpenAI26DC, Theorem 1.1):

What Lean assumes for it: `Papers.OaiGraphDecompositionsIntegral.DiscreteConvexityCover` (`Basic.lean:249`)

```lean
def DiscreteConvexityCover : Sort 0 :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (r : ℝ) (D : Set (Finset X)),
    DiscreteGround X → DiscreteDensity r → DiscreteMass X r D →
    HasCoverOfCostLe (exceptionalFamily K0 D) r (1 / 2)
```

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `symbol X`: [note, V1.5] symbol table corrected: def "$X$ is a finite ground set." (The entry incorrectly makes the graph ground set universal. The abstract covering theorem allows any nonempty finite ground set.)
- run-level `symbol \calD`: [note, V1.5] symbol table corrected: type "family of subsets of a finite ground set", def "$\calD\subseteq2^X$ is a family with $\mu_r(\calD)\geq1-1/K_0$." (The recorded graph-only description excludes the arbitrary finite-ground-set family in Theorem~\ref{thm:discrete} and omits the defining simultaneous inequalities for the transfer family. The general family, arbitrary graph family, and particular source-test family must be distinguished by scope.)
- run-level `symbol G`: [note, V1.5] symbol table corrected: def "$G$ denotes a labelled graph on $[n]$." (The recorded definition restricts $G$ universally to $\calD$, although the concentration calculation tests an unrestricted source graph. Membership in $\calD$ belongs to the containment configuration, not every occurrence of $G$; the sampling law is specified by the settings.)
- run-level `symbol \mathcal C`: [note, V1.5] symbol table corrected: def "For a finite ground set $X$, a family $\mathcal C\subseteq2^X$ covers a family $\mathcal A\subseteq2^X$ if every $A\in\mathcal A$ contains some $S\in\mathcal C$." (The recorded relation only describes covers of $\calF_H$. The paper explicitly extends covering to arbitrary families on a finite ground set, including the family $\mathcal E_{K_0}(\calD)$.)
- run-level `symbol v`: [note, V1.5] symbol table corrected: type "locally bound graph vertex or vertex count", space "The vertex set of the graph under discussion in vertex uses; $\mathbb N$ in vertex-count uses.", def "$v$ denotes a vertex in set-builder expressions such as $V_+(J)=\{v\in V(J):\deg_J(v)>0\}$ and $Y_0=\{v\in V(H):\deg_H(v)>\sqrt n\}$; it also locally denotes the number of vertices of a chosen subgraph." (The recorded entry permits only a vertex of $J$. The paper also uses $v$ as a vertex of $H$ and, in the lower-bound proof, as an integer vertex count in expressions such as $n^v$ and $v/a$.)
- run-level `symbol d`: [note, V1.5] symbol table corrected: type "degeneracy parameter", def "$d$ is a nonnegative integer specifying a graph's degeneracy or an upper bound on that degeneracy, according to context." (The entry requires $d=\degen(H)$ everywhere, whereas the splitting lemma uses $d$ as a degeneracy bound for its input graph.)
- run-level `symbol a`: [note, V1.5] symbol table corrected: type "local count or candidate vertex label", space "$\mathbb Z_{\geq0}$", def "$a$ is a locally bound integer denoting an edge count, a candidate vertex label, or an added-vertex count, according to its proof context." (The recorded edge-count definition applies only in the lower-bound proof. Elsewhere $a$ denotes a candidate vertex or the number of vertices added by closure.)
- run-level `symbol m`: [note, V1.5] symbol table corrected: type "locally specified positive integer", def "$m$ is a positive integer whose definition is local to its use." (The recorded definition covers only the splitting parameter. The paper also uses $m$ for the number of vertices outside a test set and for a positive star multiplicity; these are separate local meanings.)
- run-level `symbol Y`: [note, V1.5] symbol table corrected: type "finite ground set or vertex set", space "$\{Y:Y\text{ is a finite set}\}$", def "$Y$ is the finite ground set for the subset families; in the graph application it is the vertex set held fixed by the neighborhood embedding." (The recorded vertex-set interpretation excludes the arbitrary finite ground set allowed in compression. The assembly proof additionally gives a specific deterministic construction of the graph-theoretic $Y$.)
- run-level `symbol T`: [note, V1.5] symbol table corrected: type "locally scoped requirement set or trial count", space "$2^Y\cup\mathbb N$", def "$T$ denotes a requirement set in the compression and neighborhood tests, and the number of trials needed to finish all stars in the enlarged process in the star-forest argument." (The recorded entry covers only requirement sets. The later use is a random trial count in an enlarged process, and must be read separately.)
- run-level `symbol f_{\calQ}`: [note, V1.5] symbol table corrected: space "$\{f:2^Y\to[0,1]\}$" (The defining probability is correct, but $f_{\calQ}$ is a function on $2^Y$; $[0,1]$ is the range of its evaluations.)
- run-level `symbol U`: [note, V1.5] symbol table corrected: space "$\{U:U\text{ is a finite set of vertices}\}$", def "$U$ is a set of vertices whose candidate images are tested by Hall's criterion." (The recorded domain outside $Y$ applies to transfer only. In degree embedding, $U$ consists of vertices of a layer of $J$, before they are mapped into the host bin.)
- run-level `symbol A`: [note, V1.5] symbol table corrected: type "cover-family member or positive absolute constant, according to context", space "$2^X$ in covering notation; $\mathbb R_{>0}$ in numerical estimates", def "In the covering definition, $A\in\calF_H$ is a set containing some $S\in\mathcal C$; for a general covered family, $A$ ranges over that family. In the star-forest estimates and the assembly proof, $A=400e^4$." (The recorded entry describes only the bound variable in the covering relation. The same letter later denotes the explicit constant $400e^4$, which is essential to reading the star-forest estimates and the assembly proof.)
- run-level `lem:transfer-hoeffding`: [note, V1.5] cited source checked: source supplied by the user at discovery/cited_sources/Hoeffding63.txt
- run-level `lem:transfer-hall`: [note, V1.5] cited source checked: source supplied by the user at discovery/cited_sources/Hall35.txt
- note on `lem:transfer-hall`: cited source checked: source supplied by the user at discovery/cited_sources/Hall35.txt
- note on `lem:transfer-hoeffding`: cited source checked: source supplied by the user at discovery/cited_sources/Hoeffding63.txt
- note on `symbol \calD`: symbol table corrected: type "family of subsets of a finite ground set", def "$\calD\subseteq2^X$ is a family with $\mu_r(\calD)\geq1-1/K_0$." (The recorded graph-only description excludes the arbitrary finite-ground-set family in Theorem~\ref{thm:discrete} and omits the defining simultaneous inequalities for the transfer family. The general family, arbitrary graph family, and particular source-test family must be distinguished by scope.)
- note on `symbol \mathcal C`: symbol table corrected: def "For a finite ground set $X$, a family $\mathcal C\subseteq2^X$ covers a family $\mathcal A\subseteq2^X$ if every $A\in\mathcal A$ contains some $S\in\mathcal C$." (The recorded relation only describes covers of $\calF_H$. The paper explicitly extends covering to arbitrary families on a finite ground set, including the family $\mathcal E_{K_0}(\calD)$.)
- note on `symbol a`: symbol table corrected: type "local count or candidate vertex label", space "$\mathbb Z_{\geq0}$", def "$a$ is a locally bound integer denoting an edge count, a candidate vertex label, or an added-vertex count, according to its proof context." (The recorded edge-count definition applies only in the lower-bound proof. Elsewhere $a$ denotes a candidate vertex or the number of vertices added by closure.)
- note on `symbol A`: symbol table corrected: type "cover-family member or positive absolute constant, according to context", space "$2^X$ in covering notation; $\mathbb R_{>0}$ in numerical estimates", def "In the covering definition, $A\in\calF_H$ is a set containing some $S\in\mathcal C$; for a general covered family, $A$ ranges over that family. In the star-forest estimates and the assembly proof, $A=400e^4$." (The recorded entry describes only the bound variable in the covering relation. The same letter later denotes the explicit constant $400e^4$, which is essential to reading the star-forest estimates and the assembly proof.)
- note on `symbol d`: symbol table corrected: type "degeneracy parameter", def "$d$ is a nonnegative integer specifying a graph's degeneracy or an upper bound on that degeneracy, according to context." (The entry requires $d=\degen(H)$ everywhere, whereas the splitting lemma uses $d$ as a degeneracy bound for its input graph.)
- note on `symbol f_{\calQ}`: symbol table corrected: space "$\{f:2^Y\to[0,1]\}$" (The defining probability is correct, but $f_{\calQ}$ is a function on $2^Y$; $[0,1]$ is the range of its evaluations.)
- note on `symbol G`: symbol table corrected: def "$G$ denotes a labelled graph on $[n]$." (The recorded definition restricts $G$ universally to $\calD$, although the concentration calculation tests an unrestricted source graph. Membership in $\calD$ belongs to the containment configuration, not every occurrence of $G$; the sampling law is specified by the settings.)
- note on `symbol m`: symbol table corrected: type "locally specified positive integer", def "$m$ is a positive integer whose definition is local to its use." (The recorded definition covers only the splitting parameter. The paper also uses $m$ for the number of vertices outside a test set and for a positive star multiplicity; these are separate local meanings.)
- note on `symbol T`: symbol table corrected: type "locally scoped requirement set or trial count", space "$2^Y\cup\mathbb N$", def "$T$ denotes a requirement set in the compression and neighborhood tests, and the number of trials needed to finish all stars in the enlarged process in the star-forest argument." (The recorded entry covers only requirement sets. The later use is a random trial count in an enlarged process, and must be read separately.)
- note on `symbol U`: symbol table corrected: space "$\{U:U\text{ is a finite set of vertices}\}$", def "$U$ is a set of vertices whose candidate images are tested by Hall's criterion." (The recorded domain outside $Y$ applies to transfer only. In degree embedding, $U$ consists of vertices of a layer of $J$, before they are mapped into the host bin.)
- note on `symbol v`: symbol table corrected: type "locally bound graph vertex or vertex count", space "The vertex set of the graph under discussion in vertex uses; $\mathbb N$ in vertex-count uses.", def "$v$ denotes a vertex in set-builder expressions such as $V_+(J)=\{v\in V(J):\deg_J(v)>0\}$ and $Y_0=\{v\in V(H):\deg_H(v)>\sqrt n\}$; it also locally denotes the number of vertices of a chosen subgraph." (The recorded entry permits only a vertex of $J$. The paper also uses $v$ as a vertex of $H$ and, in the lower-bound proof, as an integer vertex count in expressions such as $n^v$ and $v/a$.)
- note on `symbol X`: symbol table corrected: def "$X$ is a finite ground set." (The entry incorrectly makes the graph ground set universal. The abstract covering theorem allows any nonempty finite ground set.)
- note on `symbol Y`: symbol table corrected: type "finite ground set or vertex set", space "$\{Y:Y\text{ is a finite set}\}$", def "$Y$ is the finite ground set for the subset families; in the graph application it is the vertex set held fixed by the neighborhood embedding." (The recorded vertex-set interpretation excludes the arbitrary finite ground set allowed in compression. The assembly proof additionally gives a specific deterministic construction of the graph-theoretic $Y$.)
- note on `thm:discrete`: cited source checked: source supplied by the user at discovery/cited_sources/OpenAI26DC.txt
- note on `thm:typical-cover`: pinned reading: The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat. (Theorem~\ref{thm:discrete} explicitly allows repeated tuple members, and Corollary~\ref{cor:typical-cover} uses precisely that theorem and its exceptional family.)

### V1 lint warnings

- thm:main: thm:main references \ref{prop:transfer} (prop:transfer) but `depends_on` lacks ass:transfer-order, ass:transfer-configuration; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{prop:degree-embedding} (prop:degree-embedding) but `depends_on` lacks ass:degree-embedding-order, ass:degree-embedding-bounds, ass:degree-embedding-size; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{prop:stars} (prop:stars) but `depends_on` lacks ass:stars-order, ass:stars-size, ass:stars-support, ass:stars-small-q; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{lem:q-lower} (lem:q-lower) but `depends_on` lacks ass:q-lower-edge, ass:q-lower-order, def:q-lower-d; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{cor:typical-cover} (cor:typical-cover) but `depends_on` lacks ass:typical-cover-order, ass:typical-cover-graph, ass:typical-cover-density, ass:typical-cover-mass; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{lem:split} (lem:split) but `depends_on` lacks ass:split-count, ass:split-degeneracy; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:typical-cover: cor:typical-cover references \ref{thm:discrete} (thm:discrete) but `depends_on` lacks ass:discrete-ground, ass:discrete-density, ass:discrete-mass; V1.5 must confirm whether the paper assumes it or merely mentions it
- prop:transfer: prop:transfer references \ref{lem:compression} (lem:compression) but `depends_on` lacks ass:compression-ground, ass:compression-density, ass:compression-size, ass:compression-family; V1.5 must confirm whether the paper assumes it or merely mentions it

### Parser warnings

- main.tex:10: \input{glyphtounicode} not found (tried glyphtounicode.tex, glyphtounicode relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)
- main.tex:11: \input{glyphtounicode-cmex} not found (tried glyphtounicode-cmex.tex, glyphtounicode-cmex relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiGraphDecompositionsIntegral.main` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGraphDecompositionsIntegral.typical_cover` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGraphDecompositionsIntegral.q_lower` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGraphDecompositionsIntegral.degeneracy_split` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGraphDecompositionsIntegral.compression` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGraphDecompositionsIntegral.transfer` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGraphDecompositionsIntegral.degree_embedding` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiGraphDecompositionsIntegral.stars` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (9 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (342 object(s)) |
| `graph.json` | present (345 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 342 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (33 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`

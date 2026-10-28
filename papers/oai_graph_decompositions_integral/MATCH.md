# The corrected paper and its Lean formalization — oai_graph_decompositions_integral

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} There exist an absolute integer $k\geq2$ and an absolute constant $L\geq1$ such that, for every $n\geq2$ and every graph $H$ on at most $n$ vertices, the edges of $H$ admit a partition \[ E(H)=E(H_1)\,\dot\cup\,\cdots\,\dot\cup\,E(H_k) \quad\text{with}\quad p_c(H_i;n)\leq Lq(H;n)\qquad(1\leq i\leq k). \] The pieces may be empty and may share vertices. The partition depends only on $H,n$ and is fixed before the random host is sampled.

**Lean.** `Papers.OaiGraphDecompositionsIntegral.main` — `lean/Papers/OaiGraphDecompositionsIntegral/TMain.lean:34`

**Status.** proved in Lean, given 1 cited result(s), under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There exist an absolute integer $k\geq2$ and an absolute constant $L\geq1$ such that, for every $n\geq2$ and every graph $H$ on at most $n$ vertices, the edges of $H$ admit a partition | ≈ then `∃ k : ℕ,`<br>≈ then `2 ≤ k`<br>≈ then `∃ L : ℝ,`<br>≈ then `1 ≤ L`<br>≈ `n : ℕ`<br>≈ `H : SimpleGraph V`<br>≈ `FiniteSimpleGraphs V`<br>≈ `MainOrder n`<br>≈ `MainGraphSize V n`<br>≈ then `∃ P : Fin k → SimpleGraph V,`<br>≈ `∀ i`<br>≈ then `P i ≤ H`<br>≈ `∀ e ∈ H.edgeSet`<br>≈ then `∃! i, e ∈ (P i).edgeSet` |
| \[ E(H)=E(H_1)\,\dot\cup\,\cdots\,\dot\cup\,E(H_k) \quad\text{with}\quad | ≈ then `∃ P : Fin k → SimpleGraph V,`<br>≈ `∀ i`<br>≈ then `P i ≤ H`<br>≈ `∀ e ∈ H.edgeSet`<br>≈ then `∃! i, e ∈ (P i).edgeSet` |
| p_c(H_i;n)\leq Lq(H;n)\qquad | then `containmentThreshold (P i) n ≤ L * expectationThreshold H n` |
| (1\leq i\leq k). \] | `∀ i` |
| The pieces may be empty and may share vertices. | — (no Lean counterpart recorded) |
| The partition depends only on $H,n$ and is fixed before the random host is sampled. | — (no Lean counterpart recorded) |

A row marked ≈ was given these phrases with many rows of its result at once, not on its own.

Lean also declares what the paper leaves implicit (the objects and their types): `V : Type`, `Fintype V`, `DecidableEq V`.

Lean assumes conditions that the paper's text does not state: `hDC_of_gate : DiscreteConvexityCover`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat. → `CoveredByMembers` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:207`)
- condition of the paper: All graphs are finite and simple, → `FiniteSimpleGraphs` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:74`)
- definition of the paper: copies are not required to be induced. → `ContainsCopy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:80`)
- definition of the paper: Here $G(n,p)$ has vertex set $[n]=\{1,\ldots,n\}$, with edges present independently with probability $p$. → `randomHost` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:88`)
- definition of the paper: For a graph $J$ on at most $n$ vertices, let \[ p_c(J;n)=\min\{p\in[0,1]: \Prob(G(n,p)\text{ contains a copy of }J)\geq1/2\}. \] → `containmentThresholdRaw` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:119`)
- definition of the paper: We set $p_c(J;n)=0$ when $J$ is edgeless. → `containmentThreshold` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:128`)
- definition of the paper: To define the integral expectation threshold, put $X=E(K_n)$ and let $\calF_H\subseteq2^X$ be the increasing family of edge sets whose graphs contain $H$. → `containmentFamily` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:137`)
- definition of the paper: A family $\mathcal C\subseteq2^X$ \emph{covers} $\calF_H$ if every $A\in\calF_H$ contains some $S\in\mathcal C$. → `Covers` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:146`)
- definition of the paper: Its cost at $p$ is \[ c_p(\mathcal C)=\sum_{S\in\mathcal C}p^{|S|}. \] → `coverCost` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:160`)
- definition of the paper: For $H$ with at least one edge, define \begin{equation}\label{eq:q-definition} q(H;n)=\max\{p\in[0,1]: \calF_H\text{ has a cover }\mathcal C \text{ with }c_p(\mathcal C)\leq1/2\}. \end{equation} → `expectationThresholdRaw` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:185`)
- definition of the paper: For convenience set $q(H;n)=0$ for edgeless graphs as well. → `expectationThreshold` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:193`)
- condition of the paper: for every $n\geq2$ → `MainOrder` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:328`)
- condition of the paper: and every graph $H$ on at most $n$ vertices → `MainGraphSize` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:333`)
- definition of the paper: The \emph{degeneracy} $d=\degen(H)$ is the maximum of the minimum degrees of nonempty subgraphs of $H$. → `degeneracy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:269`)
- definition of the paper: For a graph $J$, let \[ V_+(J)=\{v\in V(J):\deg_J(v)>0\} \] be its set of nonisolated vertices. → `nonisolated` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:260`)
- definition of the paper: \label{thm:discrete} Set $K_0=2^{75}$. → `K0` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:200`)
- definition of the paper: \label{prop:stars} Put $A=400e^4$. → `starConstA` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:308`)
- definition of the paper: A star forest is a graph whose nontrivial components are stars. → `IsStarForest` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:323`)
- definition of the paper: All logarithms below are natural. → `naturalLog` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:303`)

## Theorem 2.1

**Statement.** \label{thm:discrete} Set $K_0=2^{75}$. For every nonempty finite set $X$, every $r\in(0,1)$, and every family $\calD\subseteq2^X$ with $\mu_r(\calD)\geq1-1/K_0$, the family \[ \mathcal E_{K_0}(\calD)= \{S\subseteq X:S\not\subseteq D_1\cup\cdots\cup D_{K_0} \text{ for every }D_1,\ldots,D_{K_0}\in\calD\} \] has a cover of cost at most $1/2$ at the same parameter $r$. The family $\calD$ need not be monotone, and members of a tuple may repeat.

**Lean.** no declaration

**Status.** taken from the literature as cited; not proved here.

**Taken from the literature: OpenAI26DC, Theorem 1.1.**

What Lean assumes for it: `Papers.OaiGraphDecompositionsIntegral.DiscreteConvexityCover` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:249`)

```lean
def DiscreteConvexityCover : Sort 0 :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (r : ℝ) (D : Set (Finset X)),
    DiscreteGround X → DiscreteDensity r → DiscreteMass X r D →
    HasCoverOfCostLe (exceptionalFamily K0 D) r (1 / 2)
```

## Corollary 2.2

**Statement.** \label{cor:typical-cover} Let $n\geq2$, let $H$ have an edge and at most $n$ vertices, and suppose $q(H;n)<r<1$. If a family of graphs on $[n]$ satisfies $\mu_r(\calD)\geq1-1/K_0$, then some copy of $H$ has its edges contained in the union of $K_0$ members of $\calD$.

**Lean.** `Papers.OaiGraphDecompositionsIntegral.typical_cover` — `lean/Papers/OaiGraphDecompositionsIntegral/TTypicalCover.lean:20`

**Status.** proved in Lean, given 1 cited result(s), under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $n\geq2$, let $H$ have an edge and at most $n$ vertices, | `n : ℕ`<br>`H : SimpleGraph V`<br>`hfinite : FiniteSimpleGraphs V`<br>`hn : TypicalCoverOrder n`<br>`hH : TypicalCoverGraph H n` |
| and suppose $q(H;n)<r<1$. | `r : ℝ`<br>`hr : TypicalCoverDensity H n r` |
| If a family of graphs on $[n]$ satisfies $\mu_r(\calD)\geq1-1/K_0$, | `D : Set (Finset (KEdge n))`<br>`hD : TypicalCoverMass n r D` |
| then some copy of $H$ has its edges contained in the union of $K_0$ members of $\calD$. | then `∃ f : V ↪ Fin n, CoveredByMembers K0 D (copyEdges H f)` |

Lean also declares what the paper leaves implicit (the objects and their types): `V : Type`, `Fintype V`.

Lean assumes conditions that the paper's text does not state: `hDC_of_gate : DiscreteConvexityCover`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: The members $D_1,\ldots,D_{K_0}\in\calD$ in the union $D_1\cup\cdots\cup D_{K_0}$ may repeat. → `CoveredByMembers` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:207`)
- condition of the paper: All graphs are finite and simple, → `FiniteSimpleGraphs` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:74`)
- definition of the paper: copies are not required to be induced. → `ContainsCopy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:80`)
- definition of the paper: Here $G(n,p)$ has vertex set $[n]=\{1,\ldots,n\}$, with edges present independently with probability $p$. → `randomHost` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:88`)
- definition of the paper: For a graph $J$ on at most $n$ vertices, let \[ p_c(J;n)=\min\{p\in[0,1]: \Prob(G(n,p)\text{ contains a copy of }J)\geq1/2\}. \] → `containmentThresholdRaw` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:119`)
- definition of the paper: We set $p_c(J;n)=0$ when $J$ is edgeless. → `containmentThreshold` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:128`)
- definition of the paper: To define the integral expectation threshold, put $X=E(K_n)$ and let $\calF_H\subseteq2^X$ be the increasing family of edge sets whose graphs contain $H$. → `containmentFamily` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:137`)
- definition of the paper: A family $\mathcal C\subseteq2^X$ \emph{covers} $\calF_H$ if every $A\in\calF_H$ contains some $S\in\mathcal C$. → `Covers` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:146`)
- definition of the paper: Its cost at $p$ is \[ c_p(\mathcal C)=\sum_{S\in\mathcal C}p^{|S|}. \] → `coverCost` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:160`)
- definition of the paper: For $H$ with at least one edge, define \begin{equation}\label{eq:q-definition} q(H;n)=\max\{p\in[0,1]: \calF_H\text{ has a cover }\mathcal C \text{ with }c_p(\mathcal C)\leq1/2\}. \end{equation} → `expectationThresholdRaw` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:185`)
- definition of the paper: For convenience set $q(H;n)=0$ for edgeless graphs as well. → `expectationThreshold` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:193`)
- definition of the paper: For a finite ground set $X$, write $\mu_r$ for the law of its Bernoulli-$r$ random subset. → `productMeasure` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:59`)
- definition of the paper: \label{thm:discrete} Set $K_0=2^{75}$. → `K0` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:200`)
- condition of the paper: Let $n\geq2$ → `TypicalCoverOrder` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:339`)
- condition of the paper: let $H$ have an edge and at most $n$ vertices → `TypicalCoverGraph` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:345`)
- condition of the paper: and suppose $q(H;n)<r<1$. → `TypicalCoverDensity` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:354`)
- condition of the paper: If a family of graphs on $[n]$ satisfies $\mu_r(\calD)\geq1-1/K_0$ → `TypicalCoverMass` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:363`)

**Taken from the literature: OpenAI26DC, Theorem 1.1.**

What Lean assumes for it: `Papers.OaiGraphDecompositionsIntegral.DiscreteConvexityCover` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:249`)

```lean
def DiscreteConvexityCover : Sort 0 :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (r : ℝ) (D : Set (Finset X)),
    DiscreteGround X → DiscreteDensity r → DiscreteMass X r D →
    HasCoverOfCostLe (exceptionalFamily K0 D) r (1 / 2)
```

## Lemma 2.3

**Statement.** \label{lem:q-lower} If $H$ has an edge, $|V(H)|\leq n$, and $d=\degen(H)$, then \begin{equation}\label{eq:q-lower} q(H;n)\geq\frac1{2\binom n2},\qquad q(H;n)\geq\frac12 n^{-2/d}. \end{equation}

**Lean.** `Papers.OaiGraphDecompositionsIntegral.q_lower` — `lean/Papers/OaiGraphDecompositionsIntegral/Helpers/QLower.lean:247`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| If $H$ has an edge, $\|V(H)\|\leq n$, | `H : SimpleGraph V`<br>`n : ℕ`<br>`hedge : QLowerEdge H`<br>`hsize : QLowerOrder V n` |
| and $d=\degen(H)$, | — (no Lean counterpart recorded) |
| then \begin{equation} q(H;n)\geq\frac1{2\binom n2},\qquad | then `1 / (2 * (n.choose 2 : ℝ)) ≤ expectationThreshold H n` |
| q(H;n)\geq\frac12 n^{-2/d}. \end{equation} | then `(1 / 2 : ℝ) * (n : ℝ) ^ (-(2 : ℝ) / (qLowerDegeneracy H : ℝ)) ≤ expectationThreshold H n` |

Lean also declares what the paper leaves implicit (the objects and their types): `V : Type`, `Fintype V`.

Lean assumes conditions that the paper's text does not state: `hfinite : FiniteSimpleGraphs V`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: All graphs are finite and simple, → `FiniteSimpleGraphs` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:74`)
- definition of the paper: copies are not required to be induced. → `ContainsCopy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:80`)
- definition of the paper: Here $G(n,p)$ has vertex set $[n]=\{1,\ldots,n\}$, with edges present independently with probability $p$. → `randomHost` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:88`)
- definition of the paper: For a graph $J$ on at most $n$ vertices, let \[ p_c(J;n)=\min\{p\in[0,1]: \Prob(G(n,p)\text{ contains a copy of }J)\geq1/2\}. \] → `containmentThresholdRaw` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:119`)
- definition of the paper: We set $p_c(J;n)=0$ when $J$ is edgeless. → `containmentThreshold` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:128`)
- definition of the paper: To define the integral expectation threshold, put $X=E(K_n)$ and let $\calF_H\subseteq2^X$ be the increasing family of edge sets whose graphs contain $H$. → `containmentFamily` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:137`)
- definition of the paper: A family $\mathcal C\subseteq2^X$ \emph{covers} $\calF_H$ if every $A\in\calF_H$ contains some $S\in\mathcal C$. → `Covers` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:146`)
- definition of the paper: Its cost at $p$ is \[ c_p(\mathcal C)=\sum_{S\in\mathcal C}p^{|S|}. \] → `coverCost` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:160`)
- definition of the paper: For $H$ with at least one edge, define \begin{equation}\label{eq:q-definition} q(H;n)=\max\{p\in[0,1]: \calF_H\text{ has a cover }\mathcal C \text{ with }c_p(\mathcal C)\leq1/2\}. \end{equation} → `expectationThresholdRaw` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:185`)
- definition of the paper: For convenience set $q(H;n)=0$ for edgeless graphs as well. → `expectationThreshold` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:193`)
- definition of the paper: The \emph{degeneracy} $d=\degen(H)$ is the maximum of the minimum degrees of nonempty subgraphs of $H$. → `degeneracy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:269`)
- definition of the paper: $d=\degen(H)$ → `qLowerDegeneracy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:278`)
- condition of the paper: If $H$ has an edge → `QLowerEdge` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:369`)
- condition of the paper: $|V(H)|\leq n$ → `QLowerOrder` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:374`)

## Lemma 2.4

**Statement.** \label{lem:split} For every positive integer $m$, the edges of a $d$-degenerate graph can be partitioned into $m$ graphs, each of degeneracy at most $\lceil d/m\rceil$.

**Lean.** `Papers.OaiGraphDecompositionsIntegral.degeneracy_split` — `lean/Papers/OaiGraphDecompositionsIntegral/Helpers/Degeneracy.lean:212`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every positive integer $m$, the edges of a $d$-degenerate graph can be partitioned into $m$ graphs, each of degeneracy at most $\lceil d/m\rceil$. | `H : SimpleGraph V`<br>`d m : ℕ`<br>`hm : SplitCount m`<br>`hd : SplitDegeneracy H d`<br>then `∃ P : Fin m → SimpleGraph V,`<br>`∀ i`<br>then `P i ≤ H`<br>`∀ e ∈ H.edgeSet`<br>then `∃! i, e ∈ (P i).edgeSet`<br>`∀ i`<br>then `degeneracy (P i) ≤ (d + m - 1) / m` |

Lean also declares what the paper leaves implicit (the objects and their types): `V : Type`, `Fintype V`.

Lean assumes conditions that the paper's text does not state: `hfinite : FiniteSimpleGraphs V`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: All graphs are finite and simple, → `FiniteSimpleGraphs` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:74`)
- definition of the paper: The \emph{degeneracy} $d=\degen(H)$ is the maximum of the minimum degrees of nonempty subgraphs of $H$. → `degeneracy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:269`)
- condition of the paper: For every positive integer $m$ → `SplitCount` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:380`)
- condition of the paper: a $d$-degenerate graph → `SplitDegeneracy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:386`)

## Lemma 3.1

**Statement.** \label{lem:compression} Let $Y$ be finite, $r\in(0,1)$, and $s\geq1$ an integer. For every nonempty family \[ \calR\subseteq\{T\subseteq Y:1\leq|T|\leq s\} \] there is a nonempty subfamily $\calQ\subseteq\calR$ with $|\calQ|\leq\lceil2r^{-s}\rceil$ such that \begin{equation}\label{eq:compression} S\text{ satisfies }\calR\quad\Longrightarrow\quad f_{\calQ}(S)\geq1/2. \end{equation}

**Lean.** `Papers.OaiGraphDecompositionsIntegral.compression` — `lean/Papers/OaiGraphDecompositionsIntegral/Helpers/Compression.lean:160`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $Y$ be finite, $r\in(0,1)$, | `Y : Type`<br>`r : ℝ`<br>`hground : CompressionGround Y`<br>`hr : CompressionDensity r` |
| and $s\geq1$ an integer. | `s : ℕ`<br>`hs : CompressionSize s` |
| For every nonempty family | `hR : CompressionFamily R s` |
| \[ \calR\subseteq\{T\subseteq Y:1\leq\|T\|\leq s\} \] | `R : Finset (Finset Y)`<br>`hR : CompressionFamily R s` |
| there is a nonempty subfamily $\calQ\subseteq\calR$ with $\|\calQ\|\leq\lceil2r^{-s}\rceil$ such that | then `∃ Q : Finset (Finset Y),`<br>then `Q ⊆ R`<br>then `Q.Nonempty`<br>then `(Q.card : ℝ) ≤ (⌈2 * r ^ (-(s : ℤ))⌉ : ℤ)` |
| \begin{equation} S\text{ satisfies }\calR\quad\Longrightarrow\quad f_{\calQ}(S)\geq1/2. \end{equation} | `∀ S : Finset Y`<br>`Satisfies R S`<br>then `(1 / 2 : ℝ) ≤ smoothedTest Y r Q S` |

Lean also declares what the paper leaves implicit (the objects and their types): `Fintype Y`, `DecidableEq Y`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For a finite ground set $X$, write $\mu_r$ for the law of its Bernoulli-$r$ random subset. → `productMeasure` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:59`)
- definition of the paper: For a family $\calQ$ of subsets of a finite set $Y$, say that $S\subseteq Y$ \emph{satisfies} $\calQ$ if it contains some member of $\calQ$. → `Satisfies` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:285`)
- definition of the paper: Given $r\in(0,1)$, define \begin{equation}\label{eq:smoothed-test} f_{\calQ}(S)=\Prob(S\cup Z\text{ satisfies }\calQ), \qquad Z\sim\mu_r\text{ on }Y. \end{equation} → `smoothedTest` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:294`)
- condition of the paper: Let $Y$ be finite → `CompressionGround` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:390`)
- condition of the paper: $r\in(0,1)$ → `CompressionDensity` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:395`)
- condition of the paper: and $s\geq1$ an integer. → `CompressionSize` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:401`)
- condition of the paper: For every nonempty family \[ \calR\subseteq\{T\subseteq Y:1\leq|T|\leq s\} \] → `CompressionFamily` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:409`)

## Proposition 3.2

**Statement.** \label{prop:transfer} There is an absolute integer $N_1$ such that the following holds for every $n\geq N_1$ and every $r,s$ satisfying \eqref{eq:parameters}. There exists $\calD=\calD(n,r,s)\subseteq2^{E(K_n)}$ with $\mu_r(\calD)\geq1-1/K_0$ such that, whenever \begin{itemize} \item $Y\subseteq[n]$ has $|Y|\leq n^{2/3}$; \item $J$ is a labelled bipartite graph with all edges between $Y$ and $[n]\setminus Y$, and $E(J)\subseteq E(G)$ for some $G\in\calD$; \item at most $n/8$ vertices outside $Y$ have positive degree in $J$, and all of those degrees are at most $s$; \end{itemize} one has \begin{equation}\label{eq:transfer} p_c(J;n)\leq r_*:=1-(1-r)^{32}\leq32r. \end{equation}

**Lean.** `Papers.OaiGraphDecompositionsIntegral.transfer` — `lean/Papers/OaiGraphDecompositionsIntegral/TTransfer.lean:24`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There is an absolute integer $N_1$ such that the following holds for every $n\geq N_1$ and every $r,s$ satisfying \eqref{eq:parameters}. | ≈ then `∃ N₁ : ℕ,`<br>≈ `n : ℕ`<br>≈ `r : ℝ`<br>≈ `s : ℕ`<br>≈ `TransferOrder N₁ n`<br>≈ `TransferParameters n r s` |
| There exists $\calD=\calD(n,r,s)\subseteq2^{E(K_n)}$ with $\mu_r(\calD)\geq1-1/K_0$ such that, | `let D := sourceTestFamily n r s`<br>then `1 - 1 / (K0 : ℝ) ≤ muMass (KEdge n) r D` |
| whenever \begin{itemize} \item $Y\subseteq[n]$ has $\|Y\|\leq n^{2/3}$; | `Y : Finset (Fin n)`<br>`TransferConfiguration n s D Y J` |
| \item $J$ is a labelled bipartite graph with all edges between $Y$ and $[n]\setminus Y$, | `J : SimpleGraph (Fin n)`<br>`TransferConfiguration n s D Y J` |
| and $E(J)\subseteq E(G)$ for some $G\in\calD$; | `TransferConfiguration n s D Y J` |
| \item at most $n/8$ vertices outside $Y$ have positive degree in $J$, | `TransferConfiguration n s D Y J` |
| and all of those degrees are at most $s$; \end{itemize} | `TransferConfiguration n s D Y J` |
| one has \begin{equation} p_c(J;n)\leq r_*:=1-(1-r)^{32}\leq32r. \end{equation} | then `containmentThreshold J n ≤ targetDensity r`<br>then `targetDensity r ≤ 32 * r` |

A row marked ≈ was given these phrases with many rows of its result at once, not on its own.

Lean also declares what the paper leaves implicit (the objects and their types): `DecidableRel J.Adj`.

Lean assumes conditions that the paper's text does not state: `FiniteSimpleGraphs (Fin n)`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: All graphs are finite and simple, → `FiniteSimpleGraphs` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:74`)
- definition of the paper: copies are not required to be induced. → `ContainsCopy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:80`)
- definition of the paper: Here $G(n,p)$ has vertex set $[n]=\{1,\ldots,n\}$, with edges present independently with probability $p$. → `randomHost` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:88`)
- definition of the paper: For a graph $J$ on at most $n$ vertices, let \[ p_c(J;n)=\min\{p\in[0,1]: \Prob(G(n,p)\text{ contains a copy of }J)\geq1/2\}. \] → `containmentThresholdRaw` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:119`)
- definition of the paper: We set $p_c(J;n)=0$ when $J$ is edgeless. → `containmentThreshold` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:128`)
- definition of the paper: For a finite ground set $X$, write $\mu_r$ for the law of its Bernoulli-$r$ random subset. → `productMeasure` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:59`)
- definition of the paper: \label{thm:discrete} Set $K_0=2^{75}$. → `K0` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:200`)
- definition of the paper: For a family $\calQ$ of subsets of a finite set $Y$, say that $S\subseteq Y$ \emph{satisfies} $\calQ$ if it contains some member of $\calQ$. → `Satisfies` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:285`)
- definition of the paper: Given $r\in(0,1)$, define \begin{equation}\label{eq:smoothed-test} f_{\calQ}(S)=\Prob(S\cup Z\text{ satisfies }\calQ), \qquad Z\sim\mu_r\text{ on }Y. \end{equation} → `smoothedTest` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:294`)
- condition of the paper: \begin{equation}\label{eq:parameters} 0<r<1,\qquad s\in\mathbb N,\qquad s\leq10\log n,\qquad r^s\geq n^{-1/100}. \end{equation} → `TransferParameters` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:417`)
- condition of the paper: for every $n\geq N_1$ → `TransferOrder` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:425`)
- condition of the paper: whenever \begin{itemize} \item $Y\subseteq[n]$ has $|Y|\leq n^{2/3}$; \item $J$ is a labelled bipartite graph with all edges between $Y$ and $[n]\setminus Y$, and $E(J)\subseteq E(G)$ for some $G\in\calD$; \item at most $n/8$ vertices outside $Y$ have positive degree in $J$, and all of those degrees are at most $s$; \end{itemize} → `TransferConfiguration` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:436`)
- definition of the paper: All logarithms below are natural. → `naturalLog` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:303`)

## Proposition 4.1

**Statement.** \label{prop:degree-embedding} There is an absolute integer $N_2$ such that, for $n\geq N_2$ and $r,s$ satisfying \eqref{eq:parameters}, every graph $J$ with \[ |V_+(J)|\leq n/4,\qquad \degen(J)\leq s, \qquad\Delta(J)\leq n^{2/3} \] and at most $n$ vertices satisfies $p_c(J;n)\leq r$.

**Lean.** `Papers.OaiGraphDecompositionsIntegral.degree_embedding` — `lean/Papers/OaiGraphDecompositionsIntegral/TDegreeEmbedding.lean:25`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There is an absolute integer $N_2$ such that, for $n\geq N_2$ and $r,s$ satisfying \eqref{eq:parameters}, every graph $J$ with | ≈ then `∃ N₂ : ℕ,`<br>≈ `n : ℕ`<br>≈ `r : ℝ`<br>≈ `s : ℕ`<br>≈ `DegreeEmbeddingOrder N₂ n`<br>≈ `TransferParameters n r s`<br>≈ `J : SimpleGraph V` |
| \[ \|V_+(J)\|\leq n/4,\qquad | `DegreeEmbeddingBounds J n s` |
| \degen(J)\leq s, \qquad | `DegreeEmbeddingBounds J n s` |
| \Delta(J)\leq n^{2/3} \] | `DegreeEmbeddingBounds J n s` |
| and at most $n$ vertices satisfies $p_c(J;n)\leq r$. | `FiniteSimpleGraphs V`<br>`DegreeEmbeddingSize V n`<br>then `containmentThreshold J n ≤ r` |

A row marked ≈ was given these phrases with many rows of its result at once, not on its own.

Lean also declares what the paper leaves implicit (the objects and their types): `V : Type`, `Fintype V`, `DecidableEq V`, `DecidableRel J.Adj`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: All graphs are finite and simple, → `FiniteSimpleGraphs` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:74`)
- definition of the paper: copies are not required to be induced. → `ContainsCopy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:80`)
- definition of the paper: Here $G(n,p)$ has vertex set $[n]=\{1,\ldots,n\}$, with edges present independently with probability $p$. → `randomHost` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:88`)
- definition of the paper: For a graph $J$ on at most $n$ vertices, let \[ p_c(J;n)=\min\{p\in[0,1]: \Prob(G(n,p)\text{ contains a copy of }J)\geq1/2\}. \] → `containmentThresholdRaw` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:119`)
- definition of the paper: We set $p_c(J;n)=0$ when $J$ is edgeless. → `containmentThreshold` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:128`)
- definition of the paper: For a graph $J$, let \[ V_+(J)=\{v\in V(J):\deg_J(v)>0\} \] be its set of nonisolated vertices. → `nonisolated` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:260`)
- definition of the paper: The \emph{degeneracy} $d=\degen(H)$ is the maximum of the minimum degrees of nonempty subgraphs of $H$. → `degeneracy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:269`)
- condition of the paper: \begin{equation}\label{eq:parameters} 0<r<1,\qquad s\in\mathbb N,\qquad s\leq10\log n,\qquad r^s\geq n^{-1/100}. \end{equation} → `TransferParameters` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:417`)
- condition of the paper: for $n\geq N_2$ → `DegreeEmbeddingOrder` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:447`)
- condition of the paper: every graph $J$ with \[ |V_+(J)|\leq n/4,\qquad \degen(J)\leq s, \qquad\Delta(J)\leq n^{2/3} \] → `DegreeEmbeddingBounds` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:455`)
- condition of the paper: and at most $n$ vertices → `DegreeEmbeddingSize` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:463`)
- definition of the paper: All logarithms below are natural. → `naturalLog` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:303`)

## Proposition 4.2

**Statement.** \label{prop:stars} Put $A=400e^4$. There is an absolute integer $N_3$ such that, for every $n\geq N_3$ and every star forest $J$ on at most $n$ vertices with $|V_+(J)|\leq n/100$, \begin{equation}\label{eq:star-threshold} p_c(J;n)\leq2Aq(J;n). \end{equation} If $q(J;n)<1/(2A)$, the stronger bound $p_c(J;n)\leq Aq(J;n)$ holds.

**Lean.** `Papers.OaiGraphDecompositionsIntegral.stars` — `lean/Papers/OaiGraphDecompositionsIntegral/TStars.lean:56`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Put $A=400e^4$. | — (no Lean counterpart recorded) |
| There is an absolute integer $N_3$ such that, for every $n\geq N_3$ and every star forest $J$ on at most $n$ vertices with $\|V_+(J)\|\leq n/100$, | ≈ then `∃ N₃ : ℕ,`<br>≈ `∀ n : ℕ`<br>≈ `StarsOrder N₃ n`<br>≈ `J : SimpleGraph V`<br>≈ `IsStarForest J`<br>≈ `StarsSize V n`<br>≈ `StarsSupport J n` |
| \begin{equation} p_c(J;n)\leq2Aq(J;n). \end{equation} | then `containmentThreshold J n ≤ 2 * starConstA * expectationThreshold J n` |
| If $q(J;n)<1/(2A)$, the stronger bound $p_c(J;n)\leq Aq(J;n)$ holds. | `StarsSmallQ J n`<br>then `containmentThreshold J n ≤ starConstA * expectationThreshold J n` |

A row marked ≈ was given these phrases with many rows of its result at once, not on its own.

Lean also declares what the paper leaves implicit (the objects and their types): `V : Type`, `Fintype V`, `DecidableEq V`, `DecidableRel J.Adj`.

Lean assumes conditions that the paper's text does not state: `FiniteSimpleGraphs V`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: All graphs are finite and simple, → `FiniteSimpleGraphs` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:74`)
- definition of the paper: copies are not required to be induced. → `ContainsCopy` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:80`)
- definition of the paper: Here $G(n,p)$ has vertex set $[n]=\{1,\ldots,n\}$, with edges present independently with probability $p$. → `randomHost` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:88`)
- definition of the paper: For a graph $J$ on at most $n$ vertices, let \[ p_c(J;n)=\min\{p\in[0,1]: \Prob(G(n,p)\text{ contains a copy of }J)\geq1/2\}. \] → `containmentThresholdRaw` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:119`)
- definition of the paper: We set $p_c(J;n)=0$ when $J$ is edgeless. → `containmentThreshold` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:128`)
- definition of the paper: To define the integral expectation threshold, put $X=E(K_n)$ and let $\calF_H\subseteq2^X$ be the increasing family of edge sets whose graphs contain $H$. → `containmentFamily` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:137`)
- definition of the paper: A family $\mathcal C\subseteq2^X$ \emph{covers} $\calF_H$ if every $A\in\calF_H$ contains some $S\in\mathcal C$. → `Covers` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:146`)
- definition of the paper: Its cost at $p$ is \[ c_p(\mathcal C)=\sum_{S\in\mathcal C}p^{|S|}. \] → `coverCost` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:160`)
- definition of the paper: For $H$ with at least one edge, define \begin{equation}\label{eq:q-definition} q(H;n)=\max\{p\in[0,1]: \calF_H\text{ has a cover }\mathcal C \text{ with }c_p(\mathcal C)\leq1/2\}. \end{equation} → `expectationThresholdRaw` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:185`)
- definition of the paper: For convenience set $q(H;n)=0$ for edgeless graphs as well. → `expectationThreshold` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:193`)
- definition of the paper: For a graph $J$, let \[ V_+(J)=\{v\in V(J):\deg_J(v)>0\} \] be its set of nonisolated vertices. → `nonisolated` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:260`)
- definition of the paper: \label{prop:stars} Put $A=400e^4$. → `starConstA` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:308`)
- condition of the paper: for every $n\geq N_3$ → `StarsOrder` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:468`)
- condition of the paper: on at most $n$ vertices → `StarsSize` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:473`)
- condition of the paper: with $|V_+(J)|\leq n/100$ → `StarsSupport` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:479`)
- condition of the paper: If $q(J;n)<1/(2A)$ → `StarsSmallQ` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:487`)
- definition of the paper: A star forest is a graph whose nontrivial components are stars. → `IsStarForest` (`lean/Papers/OaiGraphDecompositionsIntegral/Basic.lean:323`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `main.tex:80-91` | `Papers.OaiGraphDecompositionsIntegral.main` |
| Theorem 2.1 | `thm:discrete` | `thm:discrete` | `main.tex:185-198` | — |
| Corollary 2.2 | `thm:typical-cover` | `cor:typical-cover` | `main.tex:200-205` | `Papers.OaiGraphDecompositionsIntegral.typical_cover` |
| Lemma 2.3 | `lem:q-lower` | `lem:q-lower` | `main.tex:238-244` | `Papers.OaiGraphDecompositionsIntegral.q_lower` |
| Lemma 2.4 | `lem:split` | `lem:split` | `main.tex:258-262` | `Papers.OaiGraphDecompositionsIntegral.degeneracy_split` |
| Lemma 3.1 | `lem:compression` | `lem:compression` | `main.tex:298-311` | `Papers.OaiGraphDecompositionsIntegral.compression` |
| Proposition 3.2 | `prop:transfer` | `prop:transfer` | `main.tex:346-364` | `Papers.OaiGraphDecompositionsIntegral.transfer` |
| Proposition 4.1 | `prop:degree-embedding` | `prop:degree-embedding` | `main.tex:499-508` | `Papers.OaiGraphDecompositionsIntegral.degree_embedding` |
| Proposition 4.2 | `prop:stars` | `prop:stars` | `main.tex:587-596` | `Papers.OaiGraphDecompositionsIntegral.stars` |

# Correctness report — oai_metric_markov_cotype

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- Theorem 1.2: condition added (bookkeeping or a pinned reading)
- Corollary 6.1: condition added (bookkeeping or a pinned reading)
- Corollary 6.2: condition added (bookkeeping or a pinned reading)
- `def:stopped-walk`: ambiguous; a reading was pinned
- `def:lipschitz-constant`: ambiguous; a reading was pinned
- `\|\cdot\|_1`: notation ambiguous; a reading was pinned
- `X`: notation ambiguous; a reading was pinned
- `C`: notation ambiguous; a reading was pinned
- `x_i`: notation ambiguous; a reading was pinned
- `B`: notation ambiguous; a reading was pinned
- `w_B`: notation ambiguous; a reading was pinned
- `\mathcal B`: notation ambiguous; a reading was pinned
- `X_s`: notation ambiguous; a reading was pinned
- `p`: notation ambiguous; a reading was pinned
- `S`: notation ambiguous; a reading was pinned
- `\E_i`: notation ambiguous; a reading was pinned
- `y_i`: notation ambiguous; a reading was pinned
- `e`: notation ambiguous; a reading was pinned
- `R`: notation ambiguous; a reading was pinned
- `M_m`: notation ambiguous; a reading was pinned
- `\calF_m`: notation ambiguous; a reading was pinned
- `M_\infty`: notation ambiguous; a reading was pinned
- `J`: notation ambiguous; a reading was pinned
- `f`: notation ambiguous; a reading was pinned
- `M`: notation ambiguous; a reading was pinned

7 result(s) of the paper were examined. None was found wrong as printed. In Lean: 7 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**How a statement is read.**

- **Theorem 1.2.** In the cost identities, $B=\sum_i\pi_i\|z_i-\Phi(h_i)\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices.
- **Corollary 6.2.** $\Lip(f)=\inf\{L\geq0:d(f(x),f(y))\leq Ld(x,y)\text{ for all }x,y\text{ in the domain of }f\}$, with $\inf\varnothing=\infty$.

**Notation.**

- $\|\cdot\|_1$: $\|x\|_1$ denotes the sum of the absolute values or moduli of the coordinates in the scalar sequence space containing $x$. In Corollary~\ref{cor:complex}: For $x\in\ell_1(\mathbb C)$, $\|x\|_1$ uses complex moduli, whereas $\|Jx\|_1$ is the real sequence norm on $\ell_1(\R)$.
- $X$: $X$ denotes the metric space whose metric Markov cotype or point configuration is under consideration. In Theorem~\ref{thm:main}: $X=\ell_1$ over the real scalars, equipped with its norm metric. In Corollary~\ref{cor:complex}: The space whose cotype is asserted is $X=\ell_1(\mathbb C)$ with its norm metric; the application of the real theorem uses $\ell_1(\R)$.
- $C$: $C>0$ is an admissible metric Markov cotype two constant for $(X,d)$: the same $C$ works in \eqref{eq:cotype} for every $n,t\in\N$, probability vector $\pi$, stochastic matrix $A$ reversible with respect to $\pi$, and choice $x_1,\ldots,x_n\in X$, with the points $y_1,\ldots,y_n\in X$ allowed to depend on these data. In Theorem~\ref{thm:main}: For $X=\ell_1$, the proof takes $C^2=3024$, equivalently $C=12\sqrt{21}$.
- $x_i$: The points $x_i$, indexed by $i\in[n]$, are the original input points in the ambient metric space. In Lemma~\ref{lem:cuts}, Theorem~\ref{thm:main}: The points satisfy $x_i\in\ell_1(\R)$. In Corollary~\ref{cor:complex}: The points satisfy $x_i\in\ell_1(\mathbb C)$; their images $Jx_i$ are the inputs to the real-space construction.
- $B$: The notation $B$ is overloaded between a coordinate index and the nonnegative scalar approximation cost $\sum_i\pi_i\|z_i-\Phi(h_i)\|_{1,w}^2$. In Lemma~\ref{lem:cuts}: In the cut construction, $B$ ranges over nonempty proper subsets of $[n]$; in coordinate sums, $B\in\mathcal B$, where only subsets with $w_B>0$ are retained. In Lemma~\ref{lem:flat}, Corollary~\ref{cor:martingale}: The symbol $B\in\mathcal B$ is a coordinate index in an arbitrary finite nonempty set with positive weights; no realization as a subset of $[n]$ is required. In Theorem~\ref{thm:main}: In coordinate subscripts and sums, $B\in\mathcal B$ is a retained cut index. In the cost identities and inequalities, the standalone symbol denotes $B=\sum_i\pi_i\|z_i-\Phi(h_i)\|_{1,w}^2$.
- $w_B$: $w_B>0$ for every $B\in\mathcal B$. In Lemma~\ref{lem:cuts}: $w_B=\|b_B\|_1$ for each retained cut $B\in\mathcal B$; cuts with zero weight are discarded.
- $\mathcal B$: $\mathcal B$ is a finite nonempty coordinate index set. In Lemma~\ref{lem:cuts}: $\mathcal B=\{B\subseteq[n]:B\ne\varnothing,\ B\ne[n],\ \|b_B\|_1>0\}$ in the cut construction for the noncoincident input points.
- $X_s$: $X_s$ is the state at integer time $s\geq0$ of the stationary Markov walk on $[n]$. In Theorem~\ref{thm:main}: The walk has transition matrix $A$ and stationary distribution $\pi$; $X_s$ indexes the underlying walk after $s$ live transitions, so the index at death is $X_S$.
- $p$: $p$ is a real parameter whose exponent and geometric-probability uses are local to their respective contexts. In Lemma~\ref{lem:comparison}, Theorem~\ref{thm:main}: $p=1/(t+1)$ for $t\in\N$, so $0<p\leq1/2$; it is the stopping probability and $q=1-p$.
- $S$: $S$ is local notation for a geometric number of walk steps or for a subset of a Hilbert space, according to context. In Lemma~\ref{lem:comparison}, Theorem~\ref{thm:main}: $S\in\{0,1,2,\ldots\}$ is independent of the walk and satisfies $\Prob(S=s)=pq^s$, where $p=1/(t+1)$ and $q=1-p$; it counts live walk transitions before stopping and has mean $t$. In Corollary~\ref{cor:extension}: $S$ is an arbitrary subset of $\mathcal H$, serving as the domain of $f:S\to\ell_1$.
- $\E_i$: $\E_i$ denotes expectation under the law of an $A$-walk with $X_0=i$, including the independent variable $S$ with $\Prob(S=s)=pq^s$ for $s\geq0$ when the integrand involves $S$.
- $y_i$: For $i\in[n]$, $y_i\in X$ denotes a choice of modified point in the metric Markov cotype inequality. In Theorem~\ref{thm:main}: If all $x_i$ coincide, choose $y_i=x_i$; otherwise choose $y_i=T(\Phi(h_i))$, where $h_i=p\sum_{s=0}^\infty q^s(A^s z)_i$, $p=1/(t+1)$ and $q=1-p$. In Corollary~\ref{cor:complex}: For complex input points, $y_i=J^{-1}\widetilde y_i$, where $\widetilde y_i\in\ell_1(\R)$ are the modified points obtained by applying the real construction to $Jx_i$.
- $e$: $e$ is a binary vector in $\{0,1\}^{\mathcal B}$ used as the center of the quartic potential. In Lemma~\ref{lem:flat}: $e$ is an arbitrary fixed binary vector. In Corollary~\ref{cor:martingale}: $e$ is $\calF_0$-measurable. In Theorem~\ref{thm:main}: In the stopped-walk construction, $e=z_{X_0}$ and is $\calF_0$-measurable.
- $R$: $R$ denotes a nonnegative remainder, with its definition local to its occurrence. In Lemma~\ref{lem:flat}: $R=F_e(u')-F_e(u)-4\|a\|_H^2\langle a,\delta\rangle_H=2\|a\|_H^2\|\delta\|_H^2+(2\langle a,\delta\rangle_H+\|\delta\|_H^2)^2$. In Lemma~\ref{lem:comparison}: In the proof, $R=S-t\lfloor S/t\rfloor$ takes values in $\{0,\ldots,t-1\}$, and $\Prob(R=r)=pq^r/(1-q^t)$ for $0\leq r<t$.
- $M_m$: $(M_m)_{m\geq0}$ is an $H$-valued martingale with respect to $(\calF_m)$, taking values in $Q$ and converging almost surely to $M_\infty$. In Theorem~\ref{thm:main}: $M_m$ is the value attached to the state at chain time $m$: the value is $h_i$ at an alive state of index $i$ and $z_i$ at a dead state of index $i$; in particular, $M_0=h_{X_0}$ and $M_m=z_{X_S}$ for $m\geq S+1$.
- $\calF_m$: $\calF_m$, for integers $m\geq0$, is the sigma algebra at time $m$ of the filtration with respect to which $(M_m)_{m\geq0}$ is a martingale. In Theorem~\ref{thm:main}: $\calF_m$ is generated by the initial state and the first $m$ transitions of the chain on alive and dead states, with dead states absorbing; it records no future transitions or survival trials.
- $M_\infty$: $M_\infty=\lim_{m\to\infty}M_m$ almost surely, with values in $Q$. In Theorem~\ref{thm:main}: $M_\infty=z_{X_S}$.
- $J$: The notation $J$ is local to the proof in which it occurs. In Lemma~\ref{lem:comparison}: $J=\lfloor S/t\rfloor$ is a nonnegative integer-valued random quantity defined from the geometric stopping time, and $R=S-tJ$. In Corollary~\ref{cor:complex}: $J:\ell_1(\mathbb C)\to\ell_1(\R)$ is the real-linear bijection $Jx=(\Re x(1),\Im x(1),\Re x(2),\Im x(2),\ldots)$, satisfying $\|x\|_1\leq\|Jx\|_1\leq\sqrt2\|x\|_1$.
- $f$: $f$ denotes a map between the domain and target metric spaces specified in its context. In Corollary~\ref{cor:extension}: $f:S\to\ell_1$ is Lipschitz, where $S\subseteq\mathcal H$ and $\ell_1$ is the real sequence space.
- $M$: $M>0$ is a Markov type two constant for the given metric space $(Z,d_Z)$, uniform over every $n,t\in\N$, every probability vector $\pi$, every stochastic matrix $A$ reversible with respect to $\pi$, and all $u_1,\ldots,u_n\in Z$. In Corollary~\ref{cor:extension}: For the Hilbert source $\mathcal H$, the Markov type two constant is taken to be $M=1$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.2 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_realEllOne_le` (`TMain.lean:47`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 2.1 | proved in Lean | `Papers.OaiMetricMarkovCotype.cut_decomposition` (`Helpers/Cuts.lean:569`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.1 | proved in Lean | `Papers.OaiMetricMarkovCotype.flat_cubic_bound` (`Helpers/Flat.lean:161`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 3.2 | proved in Lean | `Papers.OaiMetricMarkovCotype.martingale_cubic_energy_bound` (`TMartingale.lean:198`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.1 | proved in Lean | `Papers.OaiMetricMarkovCotype.geometric_endpoint_comparison` (`Helpers/Comparison.lean:518`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 6.1 | proved in Lean, under 1 condition(s) made explicit | `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_complexEllOne_le` (`TComplex.lean:275`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Corollary 6.2 | proved in Lean, given 1 cited result(s), under 2 condition(s) made explicit | `Papers.OaiMetricMarkovCotype.lipschitz_extension_hilbert_to_ellOne` (`TExtension.lean:69`) | the standard ones only (propext, Classical.choice, Quot.sound) |

**Taken from the literature, not proved here.**

- MendelNaor13, Corollary 1.13 — checked against source supplied by the user at discovery/cited_sources/MendelNaor13.txt

  What Lean assumes for it: `Papers.OaiMetricMarkovCotype.MendelNaorExtension` (`Basic.lean:453`)

  ```lean
  def MendelNaorExtension : Sort 0 :=
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ (_h_dual : Nonempty (RealEllOne ≃ₗᵢ[ℝ]
        StrongDual ℝ (ZeroAtInftyContinuousMap ℕ ℝ))), -- @realizes c_0(null sequences, sup norm)
      ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
        (M C : ℝ),
        0 < M → -- @realizes M(positive uniform Markov type constant)
        HasMarkovTypeTwo Z M →
        0 < C → -- @realizes C(positive uniform metric Markov cotype constant)
        HasMetricMarkovCotypeTwo RealEllOne C →
        ∀ (S : Set Z) (f : S → RealEllOne),
          (∃ L : NNReal, LipschitzWith L f) →
          ∃ F : Z → RealEllOne, (∀ x : S, F x = f x) ∧
            lipConst F ≤ ENNReal.ofReal (K₀ * M * C) * lipConst f
  ```

  The passage of the proof:

  > We use the Lipschitz extension theorem in
  > \cite[Corollary~1.13]{MendelNaor13}, extending Ball's theorem
  > \cite{Ball92}. In its Banach-space form, a source with Markov
  > type two and a dual Banach target with metric Markov cotype two
  > admit extensions with a constant bounded by a universal multiple
  > of the two corresponding constants.

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (10 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `8fb50cf9c19e4b975303e8f735a14797bf6c9af0d4895c34e741acc5eaadf9df`)
- stage completed: `5`
- results in scope: 7

| bucket | count |
| --- | --- |
| verified | 4 |
| verified_with_bookkeeping | 2 |
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
| source | `main.tex:88-93` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} The real space $\ell_1$ satisfies \[ N_2(\ell_1)\leq12\sqrt{21}. \] |
| Lean | `TMain.lean:47` — `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_realEllOne_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. `lem:cuts`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:200-222` (`lemma`, label `lem:cuts`) |
| statement | \label{lem:cuts} Given $x_1,\ldots,x_n\in\ell_1$, either all the points coincide, or there exist a finite set $\mathcal B$, positive weights $(w_B)_{B\in\mathcal B}$, binary vectors $z_i\in\{0,1\}^{\mathcal B}$, and an affine map $T:\R^{\mathcal B}\to\ell_1$ with the following properties. For \[ \\|u\\|_{1,w}=\sum_{B\in\mathcal B}w_B\|u_B\|, \qquad \\|u\\|_H^2=\sum_{B\in\mathcal B}w_Bu_B^2, \] one has \begin{align} T(z_i)&=x_i,\label{eq:reconstruct}\\ \\|x_i-x_j\\|_1 &=\\|z_i-z_j\\|_{1,w}=\\|z_i-z_j\\|_H^2, \label{eq:cut-distance}\\ \\|T(u)-T(u')\\|_1&\leq\\|u-u'\\|_{1,w} \qquad(u,u'\in\R^{\mathcal B}).\label{eq:contraction} \end{align} The space $H$ is $\R^{\mathcal B}$ with the indicated Hilbert norm. |
| appended hypothesis list | ass:cuts-data |
| Lean | `Helpers/Cuts.lean:569` — `Papers.OaiMetricMarkovCotype.cut_decomposition` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. `lem:flat`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:290-298` (`lemma`, label `lem:flat`) |
| statement | \label{lem:flat} For $u,u'\in Q$ and $e\in\{0,1\}^{\mathcal B}$, put $a=u-e$, $\delta=u'-u$, and $F_e(u)=\\|u-e\\|_H^4$. Then \begin{equation}\label{eq:flat} \\|\Phi(u')-\Phi(u)\\|_{1,w}^2 \leq108\bigl(F_e(u')-F_e(u) -4\\|a\\|_H^2\langle a,\delta\rangle_H\bigr). \end{equation} |
| appended hypothesis list | ass:flat-finite-cuts, ass:flat-positive-weights, ass:flat-arguments, ass:flat-center |
| Lean | `Helpers/Flat.lean:161` — `Papers.OaiMetricMarkovCotype.flat_cubic_bound` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. cor:martingale `thm:martingale`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:345-358` (`corollary`, label `cor:martingale`) |
| statement | \label{cor:martingale} Let $(M_m)_{m\geq0}$ be an $H$-valued martingale with respect to a filtration $(\calF_m)$, taking values in $Q$ and converging almost surely to $M_\infty$. If $e$ is an $\calF_0$-measurable binary vector, then \begin{align} \E\sum_{m=0}^\infty \\|\Phi(M_{m+1})-\Phi(M_m)\\|_{1,w}^2 &\leq108\bigl(\E\\|M_\infty-e\\|_H^4 -\E\\|M_0-e\\|_H^4\bigr)\notag\\ &\leq108\E\\|M_\infty-e\\|_H^4. \label{eq:martingale-energy} \end{align} |
| appended hypothesis list | ass:flat-finite-cuts, ass:flat-positive-weights, ass:martingale-process, ass:martingale-center |
| Lean | `TMartingale.lean:198` — `Papers.OaiMetricMarkovCotype.martingale_cubic_energy_bound` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. `lem:comparison`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:385-396` (`lemma`, label `lem:comparison`) |
| statement | \label{lem:comparison} Let $(X_s)_{s\geq0}$ be a stationary Markov chain on $[n]$, and let $x_1,\ldots,x_n$ lie in a metric space $(X,d)$. For $t\in\N$, set $p=1/(t+1)$ and $q=1-p$. If $S$ is independent of the walk and $\Prob(S=s)=pq^s$ for $s\geq0$, then \begin{equation}\label{eq:comparison} \E d(x_{X_S},x_{X_0})^2 \leq\frac{28}{t}\sum_{s=1}^t \E d(x_{X_s},x_{X_0})^2. \end{equation} |
| appended hypothesis list | ass:comparison-chain, ass:comparison-data, ass:comparison-time, ass:comparison-independence, ass:comparison-geometric-law |
| Lean | `Helpers/Comparison.lean:518` — `Papers.OaiMetricMarkovCotype.geometric_endpoint_comparison` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 6. cor:complex `thm:complex`

| field | value |
| --- | --- |
| bucket | `verified_with_bookkeeping` |
| source | `main.tex:596-599` (`corollary`, label `cor:complex`) |
| statement | \label{cor:complex} For complex scalars, $N_2(\ell_1(\mathbb C))\leq12\sqrt{42}$. |
| Lean | `TComplex.lean:275` — `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_complexEllOne_le` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1` |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 7. cor:extension `thm:extension`

| field | value |
| --- | --- |
| bucket | `conditional` |
| source | `main.tex:627-633` (`corollary`, label `cor:extension`) |
| statement | \label{cor:extension} There is a universal constant $K<\infty$ such that, for every real Hilbert space $\mathcal H$, every subset $S\subseteq\mathcal H$, and every Lipschitz map $f:S\to\ell_1$, there is an extension $F:\mathcal H\to\ell_1$ with $\Lip(F)\leq K\Lip(f)$. |
| appended hypothesis list | ass:extension-hilbert-source, ass:extension-subset, ass:extension-map |
| Lean | `TExtension.lean:69` — `Papers.OaiMetricMarkovCotype.lipschitz_extension_hilbert_to_ellOne` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | `ass:pin-1`, `ass:pin-2` |
| cited results | `lem:mendel-naor-extension` (MendelNaor13, Corollary 1.13) |
| assumed substrate gates | — |
| findings | — |

## Corrected version

3 of 7 result(s) differ from the version you provided — 0 repaired, 0 with the proof completed (no error), 3 only with a side condition or reading made explicit; the others are as printed. The Lean formalization is of the corrected version.

### `thm:main` (`main.tex:88-93`)

- as printed: \label{thm:main} The real space $\ell_1$ satisfies \[ N_2(\ell_1)\leq12\sqrt{21}. \]
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: In the cost identities, $B=\sum_i\pi_i\|z_i-\Phi(h_i)\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. — pins reading of def:stopped-walk: The stopped-walk construction explicitly defines the scalar $B$ immediately before computing the expected jumps and equation~\eqref{eq:jump-identity}.

### `thm:complex` (`main.tex:596-599`)

- as printed: \label{cor:complex} For complex scalars, $N_2(\ell_1(\mathbb C))\leq12\sqrt{42}$.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: In the cost identities, $B=\sum_i\pi_i\|z_i-\Phi(h_i)\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. — pins reading of def:stopped-walk: The stopped-walk construction explicitly defines the scalar $B$ immediately before computing the expected jumps and equation~\eqref{eq:jump-identity}.

### `thm:extension` (`main.tex:627-633`)

- as printed: \label{cor:extension} There is a universal constant $K<\infty$ such that, for every real Hilbert space $\mathcal H$, every subset $S\subseteq\mathcal H$, and every Lipschitz map $f:S\to\ell_1$, there is an extension $F:\mathcal H\to\ell_1$ with $\Lip(F)\leq K\Lip(f)$.
- corrected: statement unchanged
- no error: only a side condition or reading the referee made explicit (see below)
- side condition added by the confirming referee `ass:pin-1`: In the cost identities, $B=\sum_i\pi_i\|z_i-\Phi(h_i)\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. — pins reading of def:stopped-walk: The stopped-walk construction explicitly defines the scalar $B$ immediately before computing the expected jumps and equation~\eqref{eq:jump-identity}.
- side condition added by the confirming referee `ass:pin-2`: $\Lip(f)=\inf\{L\geq0:d(f(x),f(y))\leq Ld(x,y)\text{ for all }x,y\text{ in the domain of }f\}$, with $\inf\varnothing=\infty$. — pins reading of def:lipschitz-constant: The definition applies to maps between arbitrary metric spaces; standard Lipschitz constant notation uses this extended infimum. Corollary~\ref{cor:extension} applies it to Lipschitz maps, for which the finite infimum is attained.

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- clarification (`ass:pin-1`, used by `thm:main`): In the cost identities, $B=\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. — pins reading of def:stopped-walk: The stopped-walk construction explicitly defines the scalar $B$ immediately before computing the expected jumps and equation~\eqref{eq:jump-identity}.
- clarification (`ass:pin-2`, used by `thm:extension`): $\Lip(f)=\inf\{L\geq0:d(f(x),f(y))\leq Ld(x,y)\text{ for all }x,y\text{ in the domain of }f\}$, with $\inf\varnothing=\infty$. — pins reading of def:lipschitz-constant: The definition applies to maps between arbitrary metric spaces; standard Lipschitz constant notation uses this extended infimum. Corollary~\ref{cor:extension} applies it to Lipschitz maps, for which the finite infimum is attained.
- `def:lipschitz-constant`: pinned reading: $\Lip(f)=\inf\{L\geq0:d(f(x),f(y))\leq Ld(x,y)\text{ for all }x,y\text{ in the domain of }f\}$, with $\inf\varnothing=\infty$. (The definition applies to maps between arbitrary metric spaces; standard Lipschitz constant notation uses this extended infimum. Corollary~\ref{cor:extension} applies it to Lipschitz maps, for which the finite infimum is attained.)
- `def:stopped-walk`: pinned reading: In the cost identities, $B=\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. (The stopped-walk construction explicitly defines the scalar $B$ immediately before computing the expected jumps and equation~\eqref{eq:jump-identity}.)
- reading of the symbol `\|\cdot\|_1`: $\\|x\\|_1$ denotes the sum of the absolute values or moduli of the coordinates in the scalar sequence space containing $x$. In Corollary~\ref{cor:complex}: For $x\in\ell_1(\mathbb C)$, $\\|x\\|_1$ uses complex moduli, whereas $\\|Jx\\|_1$ is the real sequence norm on $\ell_1(\R)$. — The introduction defines the real norm at lines 59--60; the proof of Corollary~\ref{cor:complex}, lines 599--605, uses the notation on both $x$ and $Jx$.
- reading of the symbol `X`: $X$ denotes the metric space whose metric Markov cotype or point configuration is under consideration. In Theorem~\ref{thm:main}: $X=\ell_1$ over the real scalars, equipped with its norm metric. In Corollary~\ref{cor:complex}: The space whose cotype is asserted is $X=\ell_1(\mathbb C)$ with its norm metric; the application of the real theorem uses $\ell_1(\R)$. — Definition~\ref{def:cotype} introduces a general metric space; Lemma~\ref{lem:comparison} again permits any metric space. Lines 449--450 specialize to $X=\ell_1$, and Corollary~\ref{cor:complex} applies the definition to $\ell_1(\mathbb C)$.
- reading of the symbol `C`: $C>0$ is an admissible metric Markov cotype two constant for $(X,d)$: the same $C$ works in \eqref{eq:cotype} for every $n,t\in\N$, probability vector $\pi$, stochastic matrix $A$ reversible with respect to $\pi$, and choice $x_1,\ldots,x_n\in X$, with the points $y_1,\ldots,y_n\in X$ allowed to depend on these data. In Theorem~\ref{thm:main}: For $X=\ell_1$, the proof takes $C^2=3024$, equivalently $C=12\sqrt{21}$. — Definition~\ref{def:cotype} places the constant before all test-data quantifiers; the main proof concludes that \eqref{eq:cotype} holds with $C^2=3024$.
- reading of the symbol `x_i`: The points $x_i$, indexed by $i\in[n]$, are the original input points in the ambient metric space. In Lemma~\ref{lem:cuts}, Theorem~\ref{thm:main}: The points satisfy $x_i\in\ell_1(\R)$. In Corollary~\ref{cor:complex}: The points satisfy $x_i\in\ell_1(\mathbb C)$; their images $Jx_i$ are the inputs to the real-space construction. — Definition~\ref{def:cotype} quantifies $x_1,\ldots,x_n\in X$; Lemma~\ref{lem:cuts} and the construction preceding the proof of Theorem~\ref{thm:main} specialize to real $\ell_1$; the proof of Corollary~\ref{cor:complex} applies the real theorem to $Jx_i$.
- reading of the symbol `B`: The notation $B$ is overloaded between a coordinate index and the nonnegative scalar approximation cost $\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$. In Lemma~\ref{lem:cuts}: In the cut construction, $B$ ranges over nonempty proper subsets of $[n]$; in coordinate sums, $B\in\mathcal B$, where only subsets with $w_B>0$ are retained. In Lemma~\ref{lem:flat}, Corollary~\ref{cor:martingale}: The symbol $B\in\mathcal B$ is a coordinate index in an arbitrary finite nonempty set with positive weights; no realization as a subset of $[n]$ is required. In Theorem~\ref{thm:main}: In coordinate subscripts and sums, $B\in\mathcal B$ is a retained cut index. In the cost identities and inequalities, the standalone symbol denotes $B=\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$. — The proof of Lemma~\ref{lem:cuts} introduces nonempty proper subsets and retains those with positive weights; Section~\ref{sec:flat} instead fixes an arbitrary finite nonempty coordinate set; Section~\ref{sec:proof} explicitly introduces the scalar cost.
- reading of the symbol `w_B`: $w_B>0$ for every $B\in\mathcal B$. In Lemma~\ref{lem:cuts}: $w_B=\\|b_B\\|_1$ for each retained cut $B\in\mathcal B$; cuts with zero weight are discarded. — Lemma~\ref{lem:cuts} constructs the retained weights as $\\|b_B\\|_1$; Section~\ref{sec:flat} fixes arbitrary positive weights.
- reading of the symbol `\mathcal B`: $\mathcal B$ is a finite nonempty coordinate index set. In Lemma~\ref{lem:cuts}: $\mathcal B=\{B\subseteq[n]:B\ne\varnothing,\ B\ne[n],\ \\|b_B\\|_1>0\}$ in the cut construction for the noncoincident input points. — The proof of Lemma~\ref{lem:cuts} retains precisely the subsets with positive weight; Section~\ref{sec:flat} subsequently fixes an arbitrary finite nonempty set and positive weights.
- reading of the symbol `X_s`: $X_s$ is the state at integer time $s\geq0$ of the stationary Markov walk on $[n]$. In Theorem~\ref{thm:main}: The walk has transition matrix $A$ and stationary distribution $\pi$; $X_s$ indexes the underlying walk after $s$ live transitions, so the index at death is $X_S$. — Lemma~\ref{lem:comparison} introduces a stationary Markov chain on $[n]$; the stopped-walk construction uses a stationary $A$-walk and distinguishes its live transitions from the subsequent death transition.
- reading of the symbol `p`: $p$ is a real parameter whose exponent and geometric-probability uses are local to their respective contexts. In Lemma~\ref{lem:comparison}, Theorem~\ref{thm:main}: $p=1/(t+1)$ for $t\in\N$, so $0<p\leq1/2$; it is the stopping probability and $q=1-p$. — Lines 109--112 use $p$ as the exponent in $\ell_p$; line 386 sets $p=1/(t+1)$, repeated at line 455, and lines 475--478 identify it as the death-transition probability.
- reading of the symbol `S`: $S$ is local notation for a geometric number of walk steps or for a subset of a Hilbert space, according to context. In Lemma~\ref{lem:comparison}, Theorem~\ref{thm:main}: $S\in\{0,1,2,\ldots\}$ is independent of the walk and satisfies $\Prob(S=s)=pq^s$, where $p=1/(t+1)$ and $q=1-p$; it counts live walk transitions before stopping and has mean $t$. In Corollary~\ref{cor:extension}: $S$ is an arbitrary subset of $\mathcal H$, serving as the domain of $f:S\to\ell_1$. — Lines 386--387 and 462--486 define the geometric step count; lines 626--630 introduce the subset of the Hilbert space.
- reading of the symbol `\E_i`: $\E_i$ denotes expectation under the law of an $A$-walk with $X_0=i$, including the independent variable $S$ with $\Prob(S=s)=pq^s$ for $s\geq0$ when the integrand involves $S$. — The sentence following \eqref{eq:resolvent} states $h_i=\E_i z_{X_S}$ and specifies both the starting state and the independent geometric law.
- reading of the symbol `y_i`: For $i\in[n]$, $y_i\in X$ denotes a choice of modified point in the metric Markov cotype inequality. In Theorem~\ref{thm:main}: If all $x_i$ coincide, choose $y_i=x_i$; otherwise choose $y_i=T(\Phi(h_i))$, where $h_i=p\sum_{s=0}^\infty q^s(A^s z)_i$, $p=1/(t+1)$ and $q=1-p$. In Corollary~\ref{cor:complex}: For complex input points, $y_i=J^{-1}\widetilde y_i$, where $\widetilde y_i\in\ell_1(\R)$ are the modified points obtained by applying the real construction to $Jx_i$. — Definition~\ref{def:cotype} existentially quantifies the modified points. Section~\ref{sec:proof} chooses $y_i=x_i$ for coincident input points and otherwise defines them by \eqref{eq:y}; the proof of Corollary~\ref{cor:complex} pulls the real modified points back by $J^{-1}$.
- reading of the symbol `e`: $e$ is a binary vector in $\{0,1\}^{\mathcal B}$ used as the center of the quartic potential. In Lemma~\ref{lem:flat}: $e$ is an arbitrary fixed binary vector. In Corollary~\ref{cor:martingale}: $e$ is $\calF_0$-measurable. In Theorem~\ref{thm:main}: In the stopped-walk construction, $e=z_{X_0}$ and is $\calF_0$-measurable. — Lemma~\ref{lem:flat} permits any binary center; Corollary~\ref{cor:martingale} requires $\calF_0$-measurability; the stopped-walk construction in the proof of Theorem~\ref{thm:main} chooses $e=z_{X_0}$.
- reading of the symbol `R`: $R$ denotes a nonnegative remainder, with its definition local to its occurrence. In Lemma~\ref{lem:flat}: $R=F_e(u')-F_e(u)-4\\|a\\|_H^2\langle a,\delta\rangle_H=2\\|a\\|_H^2\\|\delta\\|_H^2+(2\langle a,\delta\rangle_H+\\|\delta\\|_H^2)^2$. In Lemma~\ref{lem:comparison}: In the proof, $R=S-t\lfloor S/t\rfloor$ takes values in $\{0,\ldots,t-1\}$, and $\Prob(R=r)=pq^r/(1-q^t)$ for $0\leq r<t$. — The proof of Lemma~\ref{lem:flat} defines $R$ by \eqref{eq:flat} and expands it in \eqref{eq:remainder}; the proof of Lemma~\ref{lem:comparison} defines $R=S-tJ$.
- reading of the symbol `M_m`: $(M_m)_{m\geq0}$ is an $H$-valued martingale with respect to $(\calF_m)$, taking values in $Q$ and converging almost surely to $M_\infty$. In Theorem~\ref{thm:main}: $M_m$ is the value attached to the state at chain time $m$: the value is $h_i$ at an alive state of index $i$ and $z_i$ at a dead state of index $i$; in particular, $M_0=h_{X_0}$ and $M_m=z_{X_S}$ for $m\geq S+1$. — Corollary~\ref{cor:martingale} specifies the general process; the attached-value construction in the main proof specifies its particular realization and chain-time indexing.
- reading of the symbol `\calF_m`: $\calF_m$, for integers $m\geq0$, is the sigma algebra at time $m$ of the filtration with respect to which $(M_m)_{m\geq0}$ is a martingale. In Theorem~\ref{thm:main}: $\calF_m$ is generated by the initial state and the first $m$ transitions of the chain on alive and dead states, with dead states absorbing; it records no future transitions or survival trials. — Corollary~\ref{cor:martingale} introduces the filtration at lines 343--347. The proof of Theorem~\ref{thm:main} specifies at lines 475--480 that it records the initial state and the first $m$ transitions only.
- reading of the symbol `M_\infty`: $M_\infty=\lim_{m\to\infty}M_m$ almost surely, with values in $Q$. In Theorem~\ref{thm:main}: $M_\infty=z_{X_S}$. — The opening sentence of Corollary~\ref{cor:martingale} specifies almost sure convergence; the display following the attached-value construction identifies the limit in the main proof.
- reading of the symbol `J`: The notation $J$ is local to the proof in which it occurs. In Lemma~\ref{lem:comparison}: $J=\lfloor S/t\rfloor$ is a nonnegative integer-valued random quantity defined from the geometric stopping time, and $R=S-tJ$. In Corollary~\ref{cor:complex}: $J:\ell_1(\mathbb C)\to\ell_1(\R)$ is the real-linear bijection $Jx=(\Re x(1),\Im x(1),\Re x(2),\Im x(2),\ldots)$, satisfying $\\|x\\|_1\leq\\|Jx\\|_1\leq\sqrt2\\|x\\|_1$. — The proof of Lemma~\ref{lem:comparison} defines $J=\lfloor S/t\rfloor$; the proof of Corollary~\ref{cor:complex} explicitly introduces the real-linear bijection $J$.
- reading of the symbol `f`: $f$ denotes a map between the domain and target metric spaces specified in its context. In Corollary~\ref{cor:extension}: $f:S\to\ell_1$ is Lipschitz, where $S\subseteq\mathcal H$ and $\ell_1$ is the real sequence space. — Lines 125--127 define the notation for arbitrary maps between metric spaces; lines 626--630 specify the domain and target in the extension application.
- reading of the symbol `M`: $M>0$ is a Markov type two constant for the given metric space $(Z,d_Z)$, uniform over every $n,t\in\N$, every probability vector $\pi$, every stochastic matrix $A$ reversible with respect to $\pi$, and all $u_1,\ldots,u_n\in Z$. In Corollary~\ref{cor:extension}: For the Hilbert source $\mathcal H$, the Markov type two constant is taken to be $M=1$. — Lines 612--621 give the defining inequality, its universal quantifiers, and the Hilbert-space choice $M=1$; the extension proof invokes that choice.

## Added conditions

| id | where | class | condition |
| --- | --- | --- | --- |
| `ass:pin-1` | `thm:main` | V1.5 bookkeeping | In the cost identities, $B=\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. (pins reading of def:stopped-walk: The stopped-walk construction explicitly defines the scalar $B$ immediately before computing the expected jumps and equation~\eqref{eq:jump-identity}.) |
| `ass:pin-1` | `thm:complex` | V1.5 bookkeeping | In the cost identities, $B=\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. (pins reading of def:stopped-walk: The stopped-walk construction explicitly defines the scalar $B$ immediately before computing the expected jumps and equation~\eqref{eq:jump-identity}.) |
| `ass:pin-1` | `thm:extension` | V1.5 bookkeeping | In the cost identities, $B=\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. (pins reading of def:stopped-walk: The stopped-walk construction explicitly defines the scalar $B$ immediately before computing the expected jumps and equation~\eqref{eq:jump-identity}.) |
| `ass:pin-2` | `thm:extension` | V1.5 bookkeeping | $\Lip(f)=\inf\{L\geq0:d(f(x),f(y))\leq Ld(x,y)\text{ for all }x,y\text{ in the domain of }f\}$, with $\inf\varnothing=\infty$. (pins reading of def:lipschitz-constant: The definition applies to maps between arbitrary metric spaces; standard Lipschitz constant notation uses this extended infimum. Corollary~\ref{cor:extension} applies it to Lipschitz maps, for which the finite infimum is attained.) |

## Conditions assumed

### Cited results

| id | used by | citation | locator | checked against |
| --- | --- | --- | --- | --- |
| `lem:mendel-naor-extension` | `thm:extension` | MendelNaor13 | Corollary 1.13 | source supplied by the user at discovery/cited_sources/MendelNaor13.txt |

`lem:mendel-naor-extension` (MendelNaor13, Corollary 1.13), invoked in the proof of `thm:extension`:

What Lean assumes for it: `Papers.OaiMetricMarkovCotype.MendelNaorExtension` (`Basic.lean:453`)

```lean
def MendelNaorExtension : Sort 0 :=
  ∃ K₀ : ℝ, 0 ≤ K₀ ∧
    ∀ (_h_dual : Nonempty (RealEllOne ≃ₗᵢ[ℝ]
      StrongDual ℝ (ZeroAtInftyContinuousMap ℕ ℝ))), -- @realizes c_0(null sequences, sup norm)
    ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
      (M C : ℝ),
      0 < M → -- @realizes M(positive uniform Markov type constant)
      HasMarkovTypeTwo Z M →
      0 < C → -- @realizes C(positive uniform metric Markov cotype constant)
      HasMetricMarkovCotypeTwo RealEllOne C →
      ∀ (S : Set Z) (f : S → RealEllOne),
        (∃ L : NNReal, LipschitzWith L f) →
        ∃ F : Z → RealEllOne, (∀ x : S, F x = f x) ∧
          lipConst F ≤ ENNReal.ofReal (K₀ * M * C) * lipConst f
```

The passage of the proof:

> We use the Lipschitz extension theorem in
> \cite[Corollary~1.13]{MendelNaor13}, extending Ball's theorem
> \cite{Ball92}. In its Banach-space form, a source with Markov
> type two and a dual Banach target with metric Markov cotype two
> admit extensions with a constant bounded by a universal multiple
> of the two corresponding constants.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `def:stopped-walk`: [note, V1.5] pinned reading: In the cost identities, $B=\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. (The stopped-walk construction explicitly defines the scalar $B$ immediately before computing the expected jumps and equation~\eqref{eq:jump-identity}.)
- run-level `def:lipschitz-constant`: [note, V1.5] pinned reading: $\Lip(f)=\inf\{L\geq0:d(f(x),f(y))\leq Ld(x,y)\text{ for all }x,y\text{ in the domain of }f\}$, with $\inf\varnothing=\infty$. (The definition applies to maps between arbitrary metric spaces; standard Lipschitz constant notation uses this extended infimum. Corollary~\ref{cor:extension} applies it to Lipschitz maps, for which the finite infimum is attained.)
- run-level `symbol \|\cdot\|_1`: [note, V1.5] symbol table corrected: space "$\ell_1(\mathbb K)\to[0,\infty)$ for $\mathbb K\in\{\R,\mathbb C\}$", def "$\\|x\\|_1=\sum_{k\geq1}\|x(k)\|$, with absolute value over real scalars and modulus over complex scalars." (The recorded domain permits only real sequences, but the complex-scalar proof also applies the norm to complex sequences. Its scalar-dependent interpretation is explicit in the displayed comparison involving $J$.)
- run-level `symbol B`: [note, V1.5] symbol table corrected: type "coordinate index or scalar approximation cost", space "A coordinate index set, or $[0,\infty)$, according to the occurrence.", def "The symbol $B$ indexes coordinates in $\mathcal B$ (nonempty proper subsets of $[n]$ in the cut construction) and is later reused for the scalar $B=\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$." (The recorded entry covers only cut indices. The flat-map section allows abstract coordinate indices, and the main construction additionally reuses $B$ for a scalar cost; these occurrences have explicitly distinguishable meanings.)
- run-level `symbol w_B`: [note, V1.5] symbol table corrected: def "Positive weights $(w_B)_{B\in\mathcal B}$ on the finite coordinate index set $\mathcal B$." (The positivity and range are correct, but the recorded definition unnecessarily requires cut vectors in the arbitrary weighted cube setting.)
- run-level `symbol \mathcal B`: [note, V1.5] symbol table corrected: type "finite nonempty index set", space "finite nonempty sets", def "A finite nonempty set $\mathcal B$ indexing the positive weights and coordinates." (The recorded subset family describes the cut construction only. The flat estimate and martingale corollary allow an arbitrary finite nonempty coordinate index set.)
- run-level `symbol p`: [note, V1.5] symbol table corrected: type "real parameter, used as a sequence-space exponent or a killing probability", space "$\{r\in\R:1<r\leq2\}$ for the sequence-space exponent; $\{1/(t+1):t\in\N\}$ for the killing probability", def "$p$ is the exponent in the introductory discussion of $\ell_p$ for $1<p\leq2$; in the geometric construction, $p=1/(t+1)$." (The recorded killing probability is correct for every listed result, but the paper also uses $p$ earlier as a sequence-space exponent. The later appearances in the geometric second-moment calculation retain the killing-probability meaning.)
- run-level `symbol S`: [note, V1.5] symbol table corrected: type "geometric step count or subset of a Hilbert space, according to context", space "$\{0,1,2,\ldots\}$ in the geometric construction; $\mathcal P(\mathcal H)$ in the extension setting", def "$S$ denotes the independent geometric number of walk steps with $\Prob(S=s)=pq^s$ for $s\geq0$, or the subset $S\subseteq\mathcal H$ on which the extension problem's map is defined." (The recorded geometric meaning is correct in the walk constructions but does not cover the later reuse of $S$ as an arbitrary Hilbert-space subset.)
- run-level `symbol \E_i`: [note, V1.5] symbol table corrected: space "Integrable real-valued random variables map to $\R$; integrable $H$-valued random variables map to $H$." (The scalar-only codomain excludes the defining use $\E_i z_{X_S}\in H$. The expectation uses the walk started at $i$ together with the independent geometric stopping variable.)
- run-level `symbol R`: [note, V1.5] symbol table corrected: type "locally defined remainder", def "In Lemma~\ref{lem:flat}, $R=F_e(u')-F_e(u)-4\\|a\\|_H^2\langle a,\delta\rangle_H$. In the proof of Lemma~\ref{lem:comparison}, $R=S-tJ$, where $J=\lfloor S/t\rfloor$." (The recorded quartic remainder describes only the first use. The later proof reuses $R$ for the integer remainder of the geometric stopping time modulo $t$.)
- run-level `symbol \E`: [note, V1.5] symbol table corrected: space "$L^1(\Omega;V)\to V$ for the real scalar or Banach space $V$ of the argument; also defined on nonnegative scalar random variables with values in $[0,\infty]$." (The recorded scalar-only space excludes the vector expectation $y_i=\E\,\med(x_{J_1},x_{J_2},x_{J_3})$. The paper also takes expectations of nonnegative infinite jump sums. The probability law is supplied by the setting, and conditional expectations are explicitly marked.)
- run-level `symbol J`: [note, V1.5] symbol table corrected: type "locally defined block index or real-linear bijection", space "$\{0,1,2,\ldots\}$ for the block index; $\ell_1(\mathbb C)\to\ell_1(\R)$ for the real-linear bijection", def "The notation $J$ is local to its proof: the block index is $J=\lfloor S/t\rfloor$, while the real-linear bijection is $Jx=(\Re x(1),\Im x(1),\Re x(2),\Im x(2),\ldots)$." (The recorded integer type and space cover only the endpoint comparison. The paper later reuses $J$ for a deterministic real-linear bijection, so these two meanings must be scoped separately.)
- run-level `symbol f`: [note, V1.5] symbol table corrected: type "map between metric spaces", space "$\text{maps between metric spaces}$", def "For a map $f$ between metric spaces, $\Lip(f)$ denotes the least $L\geq0$ such that $d(f(x),f(y))\leq Ld(x,y)$ for all $x,y$ in its domain." (The recorded domain and target apply to the extension application, whereas the definition of $\Lip(f)$ uses a general map between metric spaces.)
- run-level `symbol c_0`: [note, V1.5] symbol table corrected: def "$c_0$ is the real Banach space of sequences $x=(x(k))_{k\geq1}$ tending to zero, with norm $\sup_{k\geq1}\|x(k)\|$." (The recorded duality property does not identify the space and its norm. The standard notation $c_0$ in the real extension argument denotes the real null sequences with the supremum norm.)
- run-level `lem:mendel-naor-extension`: [note, V1.5] cited source checked: source supplied by the user at discovery/cited_sources/MendelNaor13.txt
- note on `def:lipschitz-constant`: pinned reading: $\Lip(f)=\inf\{L\geq0:d(f(x),f(y))\leq Ld(x,y)\text{ for all }x,y\text{ in the domain of }f\}$, with $\inf\varnothing=\infty$. (The definition applies to maps between arbitrary metric spaces; standard Lipschitz constant notation uses this extended infimum. Corollary~\ref{cor:extension} applies it to Lipschitz maps, for which the finite infimum is attained.)
- note on `def:stopped-walk`: pinned reading: In the cost identities, $B=\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. (The stopped-walk construction explicitly defines the scalar $B$ immediately before computing the expected jumps and equation~\eqref{eq:jump-identity}.)
- note on `lem:mendel-naor-extension`: cited source checked: source supplied by the user at discovery/cited_sources/MendelNaor13.txt
- note on `symbol \|\cdot\|_1`: symbol table corrected: space "$\ell_1(\mathbb K)\to[0,\infty)$ for $\mathbb K\in\{\R,\mathbb C\}$", def "$\\|x\\|_1=\sum_{k\geq1}\|x(k)\|$, with absolute value over real scalars and modulus over complex scalars." (The recorded domain permits only real sequences, but the complex-scalar proof also applies the norm to complex sequences. Its scalar-dependent interpretation is explicit in the displayed comparison involving $J$.)
- note on `symbol \E`: symbol table corrected: space "$L^1(\Omega;V)\to V$ for the real scalar or Banach space $V$ of the argument; also defined on nonnegative scalar random variables with values in $[0,\infty]$." (The recorded scalar-only space excludes the vector expectation $y_i=\E\,\med(x_{J_1},x_{J_2},x_{J_3})$. The paper also takes expectations of nonnegative infinite jump sums. The probability law is supplied by the setting, and conditional expectations are explicitly marked.)
- note on `symbol \E_i`: symbol table corrected: space "Integrable real-valued random variables map to $\R$; integrable $H$-valued random variables map to $H$." (The scalar-only codomain excludes the defining use $\E_i z_{X_S}\in H$. The expectation uses the walk started at $i$ together with the independent geometric stopping variable.)
- note on `symbol \mathcal B`: symbol table corrected: type "finite nonempty index set", space "finite nonempty sets", def "A finite nonempty set $\mathcal B$ indexing the positive weights and coordinates." (The recorded subset family describes the cut construction only. The flat estimate and martingale corollary allow an arbitrary finite nonempty coordinate index set.)
- note on `symbol B`: symbol table corrected: type "coordinate index or scalar approximation cost", space "A coordinate index set, or $[0,\infty)$, according to the occurrence.", def "The symbol $B$ indexes coordinates in $\mathcal B$ (nonempty proper subsets of $[n]$ in the cut construction) and is later reused for the scalar $B=\sum_i\pi_i\\|z_i-\Phi(h_i)\\|_{1,w}^2$." (The recorded entry covers only cut indices. The flat-map section allows abstract coordinate indices, and the main construction additionally reuses $B$ for a scalar cost; these occurrences have explicitly distinguishable meanings.)
- note on `symbol c_0`: symbol table corrected: def "$c_0$ is the real Banach space of sequences $x=(x(k))_{k\geq1}$ tending to zero, with norm $\sup_{k\geq1}\|x(k)\|$." (The recorded duality property does not identify the space and its norm. The standard notation $c_0$ in the real extension argument denotes the real null sequences with the supremum norm.)
- note on `symbol f`: symbol table corrected: type "map between metric spaces", space "$\text{maps between metric spaces}$", def "For a map $f$ between metric spaces, $\Lip(f)$ denotes the least $L\geq0$ such that $d(f(x),f(y))\leq Ld(x,y)$ for all $x,y$ in its domain." (The recorded domain and target apply to the extension application, whereas the definition of $\Lip(f)$ uses a general map between metric spaces.)
- note on `symbol J`: symbol table corrected: type "locally defined block index or real-linear bijection", space "$\{0,1,2,\ldots\}$ for the block index; $\ell_1(\mathbb C)\to\ell_1(\R)$ for the real-linear bijection", def "The notation $J$ is local to its proof: the block index is $J=\lfloor S/t\rfloor$, while the real-linear bijection is $Jx=(\Re x(1),\Im x(1),\Re x(2),\Im x(2),\ldots)$." (The recorded integer type and space cover only the endpoint comparison. The paper later reuses $J$ for a deterministic real-linear bijection, so these two meanings must be scoped separately.)
- note on `symbol p`: symbol table corrected: type "real parameter, used as a sequence-space exponent or a killing probability", space "$\{r\in\R:1<r\leq2\}$ for the sequence-space exponent; $\{1/(t+1):t\in\N\}$ for the killing probability", def "$p$ is the exponent in the introductory discussion of $\ell_p$ for $1<p\leq2$; in the geometric construction, $p=1/(t+1)$." (The recorded killing probability is correct for every listed result, but the paper also uses $p$ earlier as a sequence-space exponent. The later appearances in the geometric second-moment calculation retain the killing-probability meaning.)
- note on `symbol R`: symbol table corrected: type "locally defined remainder", def "In Lemma~\ref{lem:flat}, $R=F_e(u')-F_e(u)-4\\|a\\|_H^2\langle a,\delta\rangle_H$. In the proof of Lemma~\ref{lem:comparison}, $R=S-tJ$, where $J=\lfloor S/t\rfloor$." (The recorded quartic remainder describes only the first use. The later proof reuses $R$ for the integer remainder of the geometric stopping time modulo $t$.)
- note on `symbol S`: symbol table corrected: type "geometric step count or subset of a Hilbert space, according to context", space "$\{0,1,2,\ldots\}$ in the geometric construction; $\mathcal P(\mathcal H)$ in the extension setting", def "$S$ denotes the independent geometric number of walk steps with $\Prob(S=s)=pq^s$ for $s\geq0$, or the subset $S\subseteq\mathcal H$ on which the extension problem's map is defined." (The recorded geometric meaning is correct in the walk constructions but does not cover the later reuse of $S$ as an arbitrary Hilbert-space subset.)
- note on `symbol w_B`: symbol table corrected: def "Positive weights $(w_B)_{B\in\mathcal B}$ on the finite coordinate index set $\mathcal B$." (The positivity and range are correct, but the recorded definition unnecessarily requires cut vectors in the arbitrary weighted cube setting.)

### V1 lint warnings

- thm:martingale: cor:martingale references \ref{lem:flat} (lem:flat) but `depends_on` lacks ass:flat-arguments, ass:flat-center, def:flat-potential; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:main: thm:main references \ref{lem:comparison} (lem:comparison) but `depends_on` lacks ass:comparison-chain, ass:comparison-data, ass:comparison-time, ass:comparison-independence, ass:comparison-geometric-law, def:geometric-parameters; V1.5 must confirm whether the paper assumes it or merely mentions it
- thm:extension: the proof of cor:extension cites [Ball92, Ball's theorem] (cor:extension/proof/1/1); the transcription reads the citation as a comparison or a pointer to the cited work and made no cited node for it (The passage identifies Ball's theorem as the predecessor extended by the invoked Mendel--Naor extension theorem; it does not separately apply Ball's result.). paper: "…extending Ball's theorem \cite{Ball92}. In its Banach-space form, a source…"

### Parser warnings

- main.tex:10: \input{glyphtounicode} not found (tried glyphtounicode.tex, glyphtounicode relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)
- main.tex:11: \input{glyphtounicode-cmex} not found (tried glyphtounicode-cmex.tex, glyphtounicode-cmex relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_realEllOne_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiMetricMarkovCotype.cut_decomposition` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiMetricMarkovCotype.flat_cubic_bound` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiMetricMarkovCotype.martingale_cubic_energy_bound` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiMetricMarkovCotype.geometric_endpoint_comparison` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_complexEllOne_le` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `Papers.OaiMetricMarkovCotype.lipschitz_extension_hilbert_to_ellOne` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (8 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (231 object(s)) |
| `graph.json` | present (236 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 231 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (21 annotation(s), 1 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`

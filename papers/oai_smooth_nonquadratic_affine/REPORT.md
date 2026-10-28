# Correctness report — oai_smooth_nonquadratic_affine

**Verdict: NO ERROR FOUND**

**Paper: MINOR ISSUES — no main result is shown false or weakened**

Minor:

- `u`: notation ambiguous; a reading was pinned
- `n`: notation ambiguous; a reading was pinned
- `m`: notation ambiguous; a reading was pinned
- `F`: notation ambiguous; a reading was pinned
- `P`: notation ambiguous; a reading was pinned
- `y`: notation ambiguous; a reading was pinned
- `B`: notation ambiguous; a reading was pinned
- `C`: notation ambiguous; a reading was pinned
- `D`: notation ambiguous; a reading was pinned
- `U`: notation ambiguous; a reading was pinned
- `H`: notation ambiguous; a reading was pinned
- `k`: notation ambiguous; a reading was pinned
- `\gamma`: notation ambiguous; a reading was pinned
- `\zeta`: notation ambiguous; a reading was pinned
- `i`: notation ambiguous; a reading was pinned
- `e_i`: notation ambiguous; a reading was pinned
- `X_i`: notation ambiguous; a reading was pinned
- `s`: notation ambiguous; a reading was pinned
- `\delta`: notation ambiguous; a reading was pinned
- `f`: notation ambiguous; a reading was pinned
- `p`: notation ambiguous; a reading was pinned
- `q`: notation ambiguous; a reading was pinned
- `j`: notation ambiguous; a reading was pinned
- `M`: notation ambiguous; a reading was pinned
- `L`: notation ambiguous; a reading was pinned
- `Z`: notation ambiguous; a reading was pinned
- `G`: notation ambiguous; a reading was pinned
- `A`: notation ambiguous; a reading was pinned
- `z`: notation ambiguous; a reading was pinned
- `d`: notation ambiguous; a reading was pinned

6 result(s) of the paper were examined. None was found wrong as printed. In Lean: 6 proved, 0 taken from the literature as cited, 0 not certified, 0 not formalized.

## What was wrong and what was done

No error was found in the results examined.

## Clarifications (not errors)

Nothing in this section is an error of the paper. Each item is something the paper determines but does not say, made explicit so that the statements can be read, and formalized, in one way.

**Notation.**

- $u$: $u$ is a smooth real-valued graph function on its spatial domain, with pointwise positive definite Hessian. In Proposition~\ref{prop:reduction}: $u(x,t)=\sqrt{F(x)^2+t^2}$ on $\Omega\times\R$, with $n=m+1$. In Theorem~\ref{thm:main}: The constructed witness is $u(x,t)=\sqrt{F(|x|)^2+t^2}$ for $(x,t)\in\R^9\times\R$, using the global radial profile $F$.
- $n$: $n$ is the positive integer number of independent variables of the graph function $u$. In Proposition~\ref{prop:reduction}: $n=m+1$, where $m\geq1$. In Theorem~\ref{thm:main}: $n=10$.
- $m$: $m\geq1$ is an integer giving the number of $x$ variables, so that $(x,t)$ has $m+1$ independent variables. In Lemma~\ref{lem:local}, Lemma~\ref{lem:autonomous}, Proposition~\ref{prop:global}, Theorem~\ref{thm:main}: $m=9$.
- $F$: $F$ denotes the positive smooth function used in the graph ansatz, with the same letter also used for its radial profile when radial coordinates are adopted. In Proposition~\ref{prop:reduction}: $F$ is a spatial function $F:\Omega\to(0,\infty)$ in dimension $m$, and derivatives $D_x^2F$ are spatial derivatives. In Lemma~\ref{lem:local}, Lemma~\ref{lem:autonomous}, Lemma~\ref{lem:box}, Proposition~\ref{prop:global}, Theorem~\ref{thm:main}: $F(r)$ denotes the radial profile in dimension $m=9$, and the associated spatial function is $x\mapsto F(|x|)$; primes on $F$ denote radial derivatives.
- $P$: $P$ is the positive smooth auxiliary spatial function associated with $F$, with $P=(F/\det D_x^2F)^{(m+2)/(m+3)}$. In Proposition~\ref{prop:reduction}: $P$ is a function on the arbitrary open set $\Omega\subset\R^m$. In Lemma~\ref{lem:local}: $P$ denotes a radial profile on $0<r<\varepsilon$, normalized by $P(0)=1$, whose spatial extension is $x\mapsto P(|x|)$ for $x\in\R^9$ near the origin. In Lemma~\ref{lem:autonomous}, Lemma~\ref{lem:box}: $P$ denotes the radial profile from the local construction, continued on the maximal outward interval on which $F,P,y>0$, with spatial extension $x\mapsto P(|x|)$ in nine variables. In Proposition~\ref{prop:global}, Theorem~\ref{thm:main}: $P$ denotes the continued radial profile from the local construction; its global spatial extension is $x\mapsto P(|x|)$ on $\R^9$.
- $y$: $y(r)=F'(r)$ denotes the derivative of the radial profile with respect to $r$, rather than a spatial partial derivative of $F(x)$.
- $B$: $B(r)=r y'(r)/y(r)$ is the second logarithmic coordinate of a radial profile, defined for $r>0$ wherever $y(r)\ne0$, with the prime denoting differentiation with respect to $r$. In Lemma~\ref{lem:box}: In the vector-field and face calculations, $B$ also denotes the freely varying second coordinate of $(A,B,D)\in\mathcal B$, including the face $B=0$.
- $C$: $C(r)=-rP'(r)/P(r)$ denotes the radial logarithmic coordinate for $r>0$ wherever $P(r)\ne0$, with the prime denoting differentiation with respect to $r$.
- $D$: $D(r)=C(r)/B(r)$ is the normalized radial logarithmic coordinate, defined for $r>0$ wherever $B(r)\ne0$. In Lemma~\ref{lem:box}: In the vector-field and face calculations, $D$ also denotes the freely varying third coordinate of $(A,B,D)\in\mathcal B$; this polynomial coordinate system is evaluated even on $B=0$, without defining $D$ there by division.
- $U$: $U=\det(D^2u)(D^2u)^{-1}$ is the cofactor matrix of the Hessian with respect to all $n$ independent variables of $u$. In Proposition~\ref{prop:reduction}: $n=m+1$, and $U$ is evaluated on $\Omega\times\R$. In Theorem~\ref{thm:main}: $n=10$, and $U$ is evaluated on $\R^{10}$.
- $H$: $H(x)=D_x^2F(x)$ is the $m\times m$ spatial Hessian on $\Omega$, positive definite at every $x\in\Omega$.
- $k$: $k=m+2$ is the dimension-dependent scalar parameter. In Lemma~\ref{lem:local}, Lemma~\ref{lem:autonomous}, Proposition~\ref{prop:global}, Theorem~\ref{thm:main}: $k=11$.
- $\gamma$: $\gamma=(m+3)/(m+2)$ is a fixed exponent determined by the spatial dimension $m\geq1$. In Lemma~\ref{lem:local}, Lemma~\ref{lem:autonomous}, Proposition~\ref{prop:global}, Theorem~\ref{thm:main}: $m=9$ and $\gamma=12/11$.
- $\zeta$: $\zeta(x,t)=t/F(x)$ is a smooth real-valued function on $\Omega\times\R$.
- $i$: $i$ is a coordinate index whose range is specified by the indexed expression or summation. In Proposition~\ref{prop:reduction}: In $X_i$, $e_i$, $F_i$, $F_{ij}$, and $P_{ij}$, the spatial indices range from $1$ to $m$; in the full affine maximal equation they range from $1$ to $n=m+1$. In Theorem~\ref{thm:main}: In the displayed affine maximal equation, $1\leq i,j\leq10$.
- $e_i$: $e_i$ is the standard coordinate vector in the $i$th $x$ direction of $\R^m\times\R$, with $1\leq i\leq m$.
- $X_i$: For $(x,t)\in\Omega\times\R$ and $1\leq i\leq m$, $X_i(x,t)=e_i+\zeta(x,t)F_i(x)e_t$, where $F_i=\partial_iF$; together with $e_t$, these vectors form a pointwise basis.
- $s$: $s$ ranges over the auxiliary interval $[-\delta,\delta]$ in the integral construction; its physical radial values are $s=r^2/2\geq0$.
- $\delta$: $\delta>0$ is the half-length of the auxiliary interval $[-\delta,\delta]$, chosen sufficiently small that $M\delta\leq1/2$ and $L\delta<1$.
- $f$: $f$ is the first component of a trial pair $(f,p)\in\mathcal K$; when the pair is the constructed fixed point, it supplies the radial profile through $F(r)=f(r^2/2)$ and is smooth on $(-\delta,\delta)$.
- $p$: $p$ is the second component of a trial pair $(f,p)\in\mathcal K$; when the pair is the constructed fixed point, it supplies the radial profile through $P(r)=p(r^2/2)$ and is smooth on $(-\delta,\delta)$.
- $q$: $q$ is defined by the positive $m$th root in \eqref{eq:q} for each trial pair $(f,p)\in\mathcal K$ on $[-\delta,\delta]$; at the constructed fixed point it is smooth on $(-\delta,\delta)$ and satisfies $q(r^2/2)=y(r)/r$ for $r>0$.
- $j$: The notation $j$ has a context-dependent meaning: a coordinate index in indexed tensor expressions and a flux function in the local integral construction. In Proposition~\ref{prop:reduction}, Theorem~\ref{thm:main}: $j$ is a coordinate summation index with $1\leq j\leq n$; in the ten-dimensional equation its range is $\{1,\ldots,10\}$. In Lemma~\ref{lem:local}: $j(s)=\int_0^1 v^{m-1}p(v^2s)^{1-\gamma}\,dv$ for the current trial pair; at the fixed point, $j(r^2/2)=-y(r)^{m-1}P'(r)/(kr^m)$ for $r>0$.
- $M$: $M$ is a constant independent of $\delta$ and of the choice of $(f,p)\in\mathcal K$, such that $\|\mathcal T(f,p)-(1,1)\|_\infty\leq M\delta$ uniformly on $\mathcal K$.
- $L$: $L$ denotes a Lipschitz bound local to the construction in which it occurs. In Lemma~\ref{lem:local}: $L$ is independent of $\delta$ and satisfies $\|\mathcal T(f,p)-\mathcal T(\widetilde f,\widetilde p)\|_\infty\leq L\delta\|(f,p)-(\widetilde f,\widetilde p)\|_\infty$. In Lemma~\ref{lem:box}: $L$ is a Lipschitz constant for $V$ on the chosen bounded neighborhood of the box.
- $Z$: $Z(r)=P'(r)$ is a smooth real-valued function on the maximal outward continuation of the local solution for $r>0$ on which $F,P,y>0$, with the prime denoting differentiation with respect to $r$.
- $G$: $G(r,F,P,y)=r^8FP^{-12/11}/y^8$ is defined on the domain $r,F,P,y>0$.
- $A$: $A(r)=r y(r)/F(r)$ is the first logarithmic coordinate of a radial profile, defined for $r>0$ wherever the denominator is nonzero, with primes denoting radial derivatives. In Lemma~\ref{lem:box}: In the vector-field and face calculations, $A$ also denotes the freely varying first coordinate of $(A,B,D)\in\mathcal B$, rather than only its value along the constructed solution.
- $z$: $z$ denotes a point of $\R^3$, with coordinates corresponding to $(A,B,D)$. In Lemma~\ref{lem:box}: In the trajectory-distance argument, $z=z(\log r)$ satisfies $\dot z=V(z)$ while lying in the bounded neighborhood under consideration.
- $d$: $d=|z-\Pi z|$ is the nonnegative Euclidean distance from $z$ to $\mathcal B$. In Lemma~\ref{lem:box}: Along a trajectory $z$, $d$ depends on $\log r$ through $z$, and the differentiated quantity is $d^2$.

## What was proved in Lean, and what was not

A result is proved in Lean when a Lean declaration reviewed as stating it has a complete proof using no axiom beyond the standard ones. For a corrected result, the corrected statement is the one formalized.

| Result | Formal status | Lean declaration | Axioms |
| --- | --- | --- | --- |
| Theorem 1.1 | proved in Lean | `OaiSmoothNonquadraticAffine.exists_nonquadratic_entire_affine_maximal` (`TMain.lean:362`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 2.1 | proved in Lean | `OaiSmoothNonquadraticAffine.reduction_affineMaximal` (`TReduction.lean:271`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 3.1 | proved in Lean | `OaiSmoothNonquadraticAffine.exists_local_radial_solution` (`Helpers/Local.lean:20`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.1 | proved in Lean | `OaiSmoothNonquadraticAffine.autonomous_system_of_continuation` (`Helpers/Autonomous.lean:333`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Lemma 4.2 | proved in Lean | `OaiSmoothNonquadraticAffine.box_forward_invariant` (`Helpers/Box.lean:23`) | the standard ones only (propext, Classical.choice, Quot.sound) |
| Proposition 4.3 | proved in Lean | `OaiSmoothNonquadraticAffine.local_radial_solution_extends_globally` (`TGlobal.lean:24`) | the standard ones only (propext, Classical.choice, Quot.sound) |

The Lean development builds; it contains no `sorry`, `admit` or added axiom.

## The corrected paper

`bundle/corrected_paper/` holds the paper as it reads after the corrections, as plain source in the author's own class and layout, compiled to `bundle/corrected_paper/main.pdf` (9 pages). `bundle/MATCH.md` sets each result beside its Lean declaration; `bundle/lean/` holds the Lean code.

The mechanical checks leave nothing open.

# Technical appendix

The records behind the report above, by the run's own identifiers.

- paper: `main.tex` (source sha256 `93180efa8c5c5f923d62ea9e995d33fb28627055d89ad9af2198beb2b9e3f73e`)
- stage completed: `5`
- results in scope: 6

| bucket | count |
| --- | --- |
| verified | 6 |
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
| source | `main.tex:53-62` (`theorem`, label `thm:main`) |
| statement | \label{thm:main} There exists a nonquadratic function $u\in C^\infty(\R^{10})$ with $D^2u$ positive definite at every point such that \[ \sum_{i,j=1}^{10}U^{ij}\partial_{ij} (\det D^2u)^{-11/12}=0 \quad\hbox{on }\R^{10}, \qquad U=\det(D^2u)(D^2u)^{-1}. \] |
| Lean | `TMain.lean:362` — `OaiSmoothNonquadraticAffine.exists_nonquadratic_entire_affine_maximal` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 2. `prop:reduction`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:123-137` (`proposition`, label `prop:reduction`) |
| statement | \label{prop:reduction} Let $F,P$ be positive smooth functions on an open set $\Omega\subset\R^m$, and suppose $H=D_x^2F$ is positive definite. If \begin{equation}\label{eq:reduced} \det H=FP^{-\gamma},\qquad \tr(H^{-1}D_x^2P)+kP/F=0, \end{equation} then \[ u(x,t)=\sqrt{F(x)^2+t^2} \] has positive definite Hessian on $\Omega\times\R$ and satisfies \eqref{eq:affine} in dimension $n=m+1$. |
| appended hypothesis list | ass:reduction-dimension, ass:reduction-functions, ass:reduction-hessian, ass:reduction-system |
| Lean | `TReduction.lean:271` — `OaiSmoothNonquadraticAffine.reduction_affineMaximal` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 3. `lem:local`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:220-230` (`lemma`, label `lem:local`) |
| statement | \label{lem:local} There is $\varepsilon>0$ and a solution $F,P$ of \eqref{eq:radial} on $0<r<\varepsilon$ such that $F(\|x\|)$ and $P(\|x\|)$ extend smoothly to $\|x\|<\varepsilon$, with \[ F(0)=P(0)=1,\qquad D_x^2F(0)=I,\qquad D_x^2P(0)=-\frac{11}{9}I. \] Moreover $F,P,y,y'>0$ and $P'<0$ for $0<r<\varepsilon$. |
| Lean | `Helpers/Local.lean:20` — `OaiSmoothNonquadraticAffine.exists_local_radial_solution` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 4. `lem:autonomous`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:328-340` (`lemma`, label `lem:autonomous`) |
| statement | \label{lem:autonomous} On the interval of continuation, $A,B>0$, and the functions $A,B,D$ satisfy \begin{equation}\label{eq:autonomous} \begin{aligned} \dot A&=A(1+B-A),\\ \dot B&=B\bigl(9+A+(12/11)BD-9B\bigr),\\ \dot D&=(11-D)A-8D+BD(1-D/11). \end{aligned} \end{equation} Moreover $(A,B,D)\to(0,1,0)$ as $r\downarrow0$, and all three coordinates are positive for sufficiently small $r>0$. |
| Lean | `Helpers/Autonomous.lean:333` — `OaiSmoothNonquadraticAffine.autonomous_system_of_continuation` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 5. `lem:box`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:378-386` (`lemma`, label `lem:box`) |
| statement | \label{lem:box} The box \begin{equation}\label{eq:box} \mathcal B=[0,9/2]\times[0,7/2]\times[0,33/7] \end{equation} is forward invariant for \eqref{eq:autonomous}. The solution arising from Lemma~\ref{lem:local} lies in $\mathcal B$ throughout its interval of continuation. |
| Lean | `Helpers/Box.lean:23` — `OaiSmoothNonquadraticAffine.box_forward_invariant` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

### 6. `prop:global`

| field | value |
| --- | --- |
| bucket | `verified` |
| source | `main.tex:429-433` (`proposition`, label `prop:global`) |
| statement | \label{prop:global} The solution in Lemma~\ref{lem:local} extends to every $r>0$, with $F,P,y,y'>0$. Its radial extensions to $\R^9$ are smooth, and $D_x^2F$ is positive definite everywhere. |
| Lean | `TGlobal.lean:24` — `OaiSmoothNonquadraticAffine.local_radial_solution_extends_globally` |
| crosswalk verdict | `equivalent` |
| axioms | clean — `propext`, `Classical.choice`, `Quot.sound` |
| V1.5 review | faithfulness ok · ambiguity ok · correctness ok |
| added conditions | — |
| cited results | — |
| assumed substrate gates | — |
| findings | — |

## Suggestions to the authors

Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.

- reading of the symbol `u`: $u$ is a smooth real-valued graph function on its spatial domain, with pointwise positive definite Hessian. In Proposition~\ref{prop:reduction}: $u(x,t)=\sqrt{F(x)^2+t^2}$ on $\Omega\times\R$, with $n=m+1$. In Theorem~\ref{thm:main}: The constructed witness is $u(x,t)=\sqrt{F(\|x\|)^2+t^2}$ for $(x,t)\in\R^9\times\R$, using the global radial profile $F$. — The introduction defines the graph function and the pointwise positivity convention. Proposition~\ref{prop:reduction} gives its ansatz on $\Omega\times\R$, and the proof of Theorem~\ref{thm:main} gives the entire radial construction.
- reading of the symbol `n`: $n$ is the positive integer number of independent variables of the graph function $u$. In Proposition~\ref{prop:reduction}: $n=m+1$, where $m\geq1$. In Theorem~\ref{thm:main}: $n=10$. — The introduction uses $u:\R^n\to\R$; Proposition~\ref{prop:reduction} sets $n=m+1$, and Theorem~\ref{thm:main} concerns $\R^{10}$.
- reading of the symbol `m`: $m\geq1$ is an integer giving the number of $x$ variables, so that $(x,t)$ has $m+1$ independent variables. In Lemma~\ref{lem:local}, Lemma~\ref{lem:autonomous}, Proposition~\ref{prop:global}, Theorem~\ref{thm:main}: $m=9$. — The opening of Section~\ref{sec:reduction} specifies $m\geq1$; the opening of Section~\ref{sec:local} fixes $m=9$ from that point onward.
- reading of the symbol `F`: $F$ denotes the positive smooth function used in the graph ansatz, with the same letter also used for its radial profile when radial coordinates are adopted. In Proposition~\ref{prop:reduction}: $F$ is a spatial function $F:\Omega\to(0,\infty)$ in dimension $m$, and derivatives $D_x^2F$ are spatial derivatives. In Lemma~\ref{lem:local}, Lemma~\ref{lem:autonomous}, Lemma~\ref{lem:box}, Proposition~\ref{prop:global}, Theorem~\ref{thm:main}: $F(r)$ denotes the radial profile in dimension $m=9$, and the associated spatial function is $x\mapsto F(\|x\|)$; primes on $F$ denote radial derivatives. — Proposition~\ref{prop:reduction} introduces $F$ on $\Omega\subset\R^m$. The radial reduction explicitly adopts the same letters for the profiles in $r=\|x\|$, and the subsequent construction fixes $m=9$.
- reading of the symbol `P`: $P$ is the positive smooth auxiliary spatial function associated with $F$, with $P=(F/\det D_x^2F)^{(m+2)/(m+3)}$. In Proposition~\ref{prop:reduction}: $P$ is a function on the arbitrary open set $\Omega\subset\R^m$. In Lemma~\ref{lem:local}: $P$ denotes a radial profile on $0<r<\varepsilon$, normalized by $P(0)=1$, whose spatial extension is $x\mapsto P(\|x\|)$ for $x\in\R^9$ near the origin. In Lemma~\ref{lem:autonomous}, Lemma~\ref{lem:box}: $P$ denotes the radial profile from the local construction, continued on the maximal outward interval on which $F,P,y>0$, with spatial extension $x\mapsto P(\|x\|)$ in nine variables. In Proposition~\ref{prop:global}, Theorem~\ref{thm:main}: $P$ denotes the continued radial profile from the local construction; its global spatial extension is $x\mapsto P(\|x\|)$ on $\R^9$. — Proposition~\ref{prop:reduction} specifies the spatial domain and reduced equations, and its proof explicitly gives the formula for $P$. The paragraph following that proof introduces radial profiles; \eqref{eq:constants}, Lemma~\ref{lem:local}, the continuation paragraph preceding \eqref{eq:regular}, and Proposition~\ref{prop:global} fix their successive domains.
- reading of the symbol `y`: $y(r)=F'(r)$ denotes the derivative of the radial profile with respect to $r$, rather than a spatial partial derivative of $F(x)$. — The radial reduction explicitly says, "Write primes for radial derivatives and $y=F'$." The local construction subsequently writes $y=rq(r^2/2)$.
- reading of the symbol `B`: $B(r)=r y'(r)/y(r)$ is the second logarithmic coordinate of a radial profile, defined for $r>0$ wherever $y(r)\ne0$, with the prime denoting differentiation with respect to $r$. In Lemma~\ref{lem:box}: In the vector-field and face calculations, $B$ also denotes the freely varying second coordinate of $(A,B,D)\in\mathcal B$, including the face $B=0$. — \eqref{eq:ratios} defines $B$ on the continuation with $F,P,y>0$. The proof following \eqref{eq:box} evaluates the vector field on arbitrary box faces.
- reading of the symbol `C`: $C(r)=-rP'(r)/P(r)$ denotes the radial logarithmic coordinate for $r>0$ wherever $P(r)\ne0$, with the prime denoting differentiation with respect to $r$. — \eqref{eq:ratios} defines $C$ on the positive continuation; the global continuation proof uses the identity $C=BD$.
- reading of the symbol `D`: $D(r)=C(r)/B(r)$ is the normalized radial logarithmic coordinate, defined for $r>0$ wherever $B(r)\ne0$. In Lemma~\ref{lem:box}: In the vector-field and face calculations, $D$ also denotes the freely varying third coordinate of $(A,B,D)\in\mathcal B$; this polynomial coordinate system is evaluated even on $B=0$, without defining $D$ there by division. — Immediately after \eqref{eq:ratios}, the paper states, "Since $B>0$, we may also set $D=C/B$." The polynomial system \eqref{eq:autonomous} supplies its ambient coordinate extension used in the box proof.
- reading of the symbol `U`: $U=\det(D^2u)(D^2u)^{-1}$ is the cofactor matrix of the Hessian with respect to all $n$ independent variables of $u$. In Proposition~\ref{prop:reduction}: $n=m+1$, and $U$ is evaluated on $\Omega\times\R$. In Theorem~\ref{thm:main}: $n=10$, and $U$ is evaluated on $\R^{10}$. — Equation~\ref{eq:affine} defines $U$ in dimension $n$; Proposition~\ref{prop:reduction} uses $n=m+1$, and Theorem~\ref{thm:main} explicitly defines the matrix in dimension ten.
- reading of the symbol `H`: $H(x)=D_x^2F(x)$ is the $m\times m$ spatial Hessian on $\Omega$, positive definite at every $x\in\Omega$. — Proposition~\ref{prop:reduction} introduces $H=D_x^2F$ and explicitly assumes it is positive definite.
- reading of the symbol `k`: $k=m+2$ is the dimension-dependent scalar parameter. In Lemma~\ref{lem:local}, Lemma~\ref{lem:autonomous}, Proposition~\ref{prop:global}, Theorem~\ref{thm:main}: $k=11$. — Section~\ref{sec:reduction} defines $k=m+2$, and \eqref{eq:constants} fixes $k=11$ for the subsequent radial construction.
- reading of the symbol `\gamma`: $\gamma=(m+3)/(m+2)$ is a fixed exponent determined by the spatial dimension $m\geq1$. In Lemma~\ref{lem:local}, Lemma~\ref{lem:autonomous}, Proposition~\ref{prop:global}, Theorem~\ref{thm:main}: $m=9$ and $\gamma=12/11$. — Section~\ref{sec:reduction} defines the formula for $m\geq1$; equation~\ref{eq:constants} fixes $m=9$ and $\gamma=12/11$ from Section~\ref{sec:local} onward.
- reading of the symbol `\zeta`: $\zeta(x,t)=t/F(x)$ is a smooth real-valued function on $\Omega\times\R$. — Proposition~\ref{prop:reduction} assumes $F>0$ on $\Omega$, and its proof sets $\zeta=t/F$ and differentiates $\zeta$.
- reading of the symbol `i`: $i$ is a coordinate index whose range is specified by the indexed expression or summation. In Proposition~\ref{prop:reduction}: In $X_i$, $e_i$, $F_i$, $F_{ij}$, and $P_{ij}$, the spatial indices range from $1$ to $m$; in the full affine maximal equation they range from $1$ to $n=m+1$. In Theorem~\ref{thm:main}: In the displayed affine maximal equation, $1\leq i,j\leq10$. — Equation~\ref{eq:affine} sums over $1\leq i,j\leq n$; the basis display in Proposition~\ref{prop:reduction} specifies $1\leq i\leq m$; Theorem~\ref{thm:main} sums to $10$.
- reading of the symbol `e_i`: $e_i$ is the standard coordinate vector in the $i$th $x$ direction of $\R^m\times\R$, with $1\leq i\leq m$. — The pointwise basis display in the proof of Proposition~\ref{prop:reduction} specifies $1\leq i\leq m$ and separates the $x$ directions from $e_t$.
- reading of the symbol `X_i`: For $(x,t)\in\Omega\times\R$ and $1\leq i\leq m$, $X_i(x,t)=e_i+\zeta(x,t)F_i(x)e_t$, where $F_i=\partial_iF$; together with $e_t$, these vectors form a pointwise basis. — The proof of Proposition~\ref{prop:reduction} explicitly introduces the pointwise basis and its index range.
- reading of the symbol `s`: $s$ ranges over the auxiliary interval $[-\delta,\delta]$ in the integral construction; its physical radial values are $s=r^2/2\geq0$. — The proof of Lemma~\ref{lem:local} defines the trial functions on both sides of zero and explains that this ensures smoothness of $f(\|x\|^2/2)$ and $p(\|x\|^2/2)$.
- reading of the symbol `\delta`: $\delta>0$ is the half-length of the auxiliary interval $[-\delta,\delta]$, chosen sufficiently small that $M\delta\leq1/2$ and $L\delta<1$. — The proof of Lemma~\ref{lem:local} introduces the interval and explicitly says to choose $M\delta\leq1/2$ and $L\delta<1$.
- reading of the symbol `f`: $f$ is the first component of a trial pair $(f,p)\in\mathcal K$; when the pair is the constructed fixed point, it supplies the radial profile through $F(r)=f(r^2/2)$ and is smooth on $(-\delta,\delta)$. — The proof of Lemma~\ref{lem:local} first introduces the radial substitution, defines the averages for continuous trial functions, and then proves smoothness of the fixed point.
- reading of the symbol `p`: $p$ is the second component of a trial pair $(f,p)\in\mathcal K$; when the pair is the constructed fixed point, it supplies the radial profile through $P(r)=p(r^2/2)$ and is smooth on $(-\delta,\delta)$. — The proof of Lemma~\ref{lem:local} first introduces the radial substitution, defines the averages for continuous trial functions, and then proves smoothness of the fixed point.
- reading of the symbol `q`: $q$ is defined by the positive $m$th root in \eqref{eq:q} for each trial pair $(f,p)\in\mathcal K$ on $[-\delta,\delta]$; at the constructed fixed point it is smooth on $(-\delta,\delta)$ and satisfies $q(r^2/2)=y(r)/r$ for $r>0$. — The proof of Lemma~\ref{lem:local} defines the average before applying the contraction theorem, proves smoothness at the fixed point, and then states $y=rq(r^2/2)>0$.
- reading of the symbol `j`: The notation $j$ has a context-dependent meaning: a coordinate index in indexed tensor expressions and a flux function in the local integral construction. In Proposition~\ref{prop:reduction}, Theorem~\ref{thm:main}: $j$ is a coordinate summation index with $1\leq j\leq n$; in the ten-dimensional equation its range is $\{1,\ldots,10\}$. In Lemma~\ref{lem:local}: $j(s)=\int_0^1 v^{m-1}p(v^2s)^{1-\gamma}\,dv$ for the current trial pair; at the fixed point, $j(r^2/2)=-y(r)^{m-1}P'(r)/(kr^m)$ for $r>0$. — Equation~\eqref{eq:affine} uses $j$ as a coordinate index; the proof of Lemma~\ref{lem:local} introduces the normalized flux and defines its extension by \eqref{eq:j}.
- reading of the symbol `M`: $M$ is a constant independent of $\delta$ and of the choice of $(f,p)\in\mathcal K$, such that $\\|\mathcal T(f,p)-(1,1)\\|_\infty\leq M\delta$ uniformly on $\mathcal K$. — The proof of Lemma~\ref{lem:local} states that there are constants $M,L$ independent of $\delta$ satisfying the displayed bounds, following uniform bounds for the averages on $\mathcal K$.
- reading of the symbol `L`: $L$ denotes a Lipschitz bound local to the construction in which it occurs. In Lemma~\ref{lem:local}: $L$ is independent of $\delta$ and satisfies $\\|\mathcal T(f,p)-\mathcal T(\widetilde f,\widetilde p)\\|_\infty\leq L\delta\\|(f,p)-(\widetilde f,\widetilde p)\\|_\infty$. In Lemma~\ref{lem:box}: $L$ is a Lipschitz constant for $V$ on the chosen bounded neighborhood of the box. — The contraction estimate in the proof of Lemma~\ref{lem:local} specifies independence of $\delta$; the proof of Lemma~\ref{lem:box} introduces a Lipschitz constant for $V$ on a bounded neighborhood of the box.
- reading of the symbol `Z`: $Z(r)=P'(r)$ is a smooth real-valued function on the maximal outward continuation of the local solution for $r>0$ on which $F,P,y>0$, with the prime denoting differentiation with respect to $r$. — Immediately before \eqref{eq:regular}, the paper specifies the maximal outward continuation on which $F,P,y>0$ and introduces $Z=P'$; the logarithmic derivative convention is introduced separately afterward.
- reading of the symbol `G`: $G(r,F,P,y)=r^8FP^{-12/11}/y^8$ is defined on the domain $r,F,P,y>0$. — The display preceding \eqref{eq:regular} defines $G$; the proof of Proposition~\ref{prop:global} explicitly identifies $r,F,P,y>0$ as the domain of that smooth system.
- reading of the symbol `A`: $A(r)=r y(r)/F(r)$ is the first logarithmic coordinate of a radial profile, defined for $r>0$ wherever the denominator is nonzero, with primes denoting radial derivatives. In Lemma~\ref{lem:box}: In the vector-field and face calculations, $A$ also denotes the freely varying first coordinate of $(A,B,D)\in\mathcal B$, rather than only its value along the constructed solution. — The paragraph preceding \eqref{eq:ratios} specifies the outward continuation with $F,P,y>0$; \eqref{eq:ratios} defines $A$. The face calculations following \eqref{eq:box} also use $A$ as a coordinate of the ambient vector field.
- reading of the symbol `z`: $z$ denotes a point of $\R^3$, with coordinates corresponding to $(A,B,D)$. In Lemma~\ref{lem:box}: In the trajectory-distance argument, $z=z(\log r)$ satisfies $\dot z=V(z)$ while lying in the bounded neighborhood under consideration. — The proof of Lemma~\ref{lem:box} first specifies $z\in\R^3$ and its projection, then uses $z$ as a trajectory of the vector field in \eqref{eq:autonomous}.
- reading of the symbol `d`: $d=\|z-\Pi z\|$ is the nonnegative Euclidean distance from $z$ to $\mathcal B$. In Lemma~\ref{lem:box}: Along a trajectory $z$, $d$ depends on $\log r$ through $z$, and the differentiated quantity is $d^2$. — The proof of Lemma~\ref{lem:box} defines the squared distance by $d^2=\|z-\Pi z\|^2$ and differentiates it along a trajectory with respect to $\log r$.

## Added conditions

None: no condition was added to the paper's own hypotheses.

## Conditions assumed

### Cited results

None: no result rests on a theorem imported from the literature.

### Deferred substrate gates

None: every substrate this run needed was built and proved.

## Unresolved / notes

- run-level `symbol u`: [note, V1.5] symbol table corrected: space "$C^\infty(\mathcal U;\R)$, where $\mathcal U\subset\R^n$ is open" (The recorded space requires an entire function in every occurrence, whereas the reduction constructs a function on $\Omega\times\R$. The explicit ansatz and its entire radial specialization must be read in their respective scopes.)
- run-level `symbol F`: [note, V1.5] symbol table corrected: space "$C^\infty(\Omega;(0,\infty))$ for the spatial function, or its positive smooth radial profile on the radial interval under consideration." (The recorded function space describes only the spatial function on Omega. Later uses explicitly denote a one-variable radial profile by the same letter, so the space and the distinction between spatial and radial derivatives must accommodate both uses.)
- run-level `symbol P`: [note, V1.5] symbol table corrected: def "The positive smooth auxiliary function satisfying $P=(F/\det D_x^2F)^{(m+2)/(m+3)}$ under the first equation of \eqref{eq:reduced}." (The recorded auxiliary-function description omits the explicit determinant formula. Later uses also employ the same letter for a one-variable radial profile rather than directly for the spatial function; the singular-profile comparison does not redefine the constructed solution.)
- run-level `symbol i`: [note, V1.5] symbol table corrected: type "coordinate or summation index", def "A coordinate index used in $U^{ij}$ and second derivatives, and in the pointwise basis $X_i=e_i+\zeta F_i e_t$." (The recorded entry describes only summation in the affine maximal equation. The paper also uses $i$ for spatial coordinates and basis vectors, with range $1$ through $m$.)
- run-level `symbol q`: [note, V1.5] symbol table corrected: type "positive continuous scalar function associated with a trial pair", space "$C([-\delta,\delta];(0,\infty))$", def "$q(s)=\left(m\int_0^1 v^{m-1}f(v^2s)p(v^2s)^{-\gamma}\,dv\right)^{1/m}$." (The recorded entry omits the defining average and gives only the value range as its space. The derivative interpretation applies to the fixed point, whereas the average is defined for every trial pair.)
- run-level `symbol j`: [note, V1.5] symbol table corrected: type "coordinate summation index or normalized flux function, according to context", space "$\{1,\ldots,n\}$ as a coordinate index; $C([-\delta,\delta];(0,\infty))$ as the local flux average", def "In coordinate sums, $j$ is the second coordinate index. In the local integral construction, $j(s)=\int_0^1 v^{m-1}p(v^2s)^{1-\gamma}\,dv$; for the constructed solution and $r>0$, $j(r^2/2)=-y(r)^{m-1}P'(r)/(kr^m)$." (The index-only entry misses the positive scalar flux function used throughout the local construction. These are separate uses of the same notation.)
- run-level `symbol \mathcal T`: [note, V1.5] symbol table corrected: def "For $(f,p)\in\mathcal K$ and $s\in[-\delta,\delta]$, $\mathcal T(f,p)(s)=\left(1+\int_0^s q(a)\,da,\ 1-k\int_0^s j(a)q(a)^{1-m}\,da\right)$, where $q,j$ are the averages associated with the input pair $(f,p)$ in \eqref{eq:q} and \eqref{eq:j}." (The recorded entry identifies the defining equation but omits the integral formula and its dependence on the input pair.)
- run-level `symbol L`: [note, V1.5] symbol table corrected: def "A Lipschitz bound chosen for the map under consideration." (The recorded definition covers only the contraction construction. The later occurrence is a separately chosen Lipschitz constant for the vector field.)
- note on `symbol \mathcal T`: symbol table corrected: def "For $(f,p)\in\mathcal K$ and $s\in[-\delta,\delta]$, $\mathcal T(f,p)(s)=\left(1+\int_0^s q(a)\,da,\ 1-k\int_0^s j(a)q(a)^{1-m}\,da\right)$, where $q,j$ are the averages associated with the input pair $(f,p)$ in \eqref{eq:q} and \eqref{eq:j}." (The recorded entry identifies the defining equation but omits the integral formula and its dependence on the input pair.)
- note on `symbol F`: symbol table corrected: space "$C^\infty(\Omega;(0,\infty))$ for the spatial function, or its positive smooth radial profile on the radial interval under consideration." (The recorded function space describes only the spatial function on Omega. Later uses explicitly denote a one-variable radial profile by the same letter, so the space and the distinction between spatial and radial derivatives must accommodate both uses.)
- note on `symbol i`: symbol table corrected: type "coordinate or summation index", def "A coordinate index used in $U^{ij}$ and second derivatives, and in the pointwise basis $X_i=e_i+\zeta F_i e_t$." (The recorded entry describes only summation in the affine maximal equation. The paper also uses $i$ for spatial coordinates and basis vectors, with range $1$ through $m$.)
- note on `symbol j`: symbol table corrected: type "coordinate summation index or normalized flux function, according to context", space "$\{1,\ldots,n\}$ as a coordinate index; $C([-\delta,\delta];(0,\infty))$ as the local flux average", def "In coordinate sums, $j$ is the second coordinate index. In the local integral construction, $j(s)=\int_0^1 v^{m-1}p(v^2s)^{1-\gamma}\,dv$; for the constructed solution and $r>0$, $j(r^2/2)=-y(r)^{m-1}P'(r)/(kr^m)$." (The index-only entry misses the positive scalar flux function used throughout the local construction. These are separate uses of the same notation.)
- note on `symbol L`: symbol table corrected: def "A Lipschitz bound chosen for the map under consideration." (The recorded definition covers only the contraction construction. The later occurrence is a separately chosen Lipschitz constant for the vector field.)
- note on `symbol P`: symbol table corrected: def "The positive smooth auxiliary function satisfying $P=(F/\det D_x^2F)^{(m+2)/(m+3)}$ under the first equation of \eqref{eq:reduced}." (The recorded auxiliary-function description omits the explicit determinant formula. Later uses also employ the same letter for a one-variable radial profile rather than directly for the spatial function; the singular-profile comparison does not redefine the constructed solution.)
- note on `symbol q`: symbol table corrected: type "positive continuous scalar function associated with a trial pair", space "$C([-\delta,\delta];(0,\infty))$", def "$q(s)=\left(m\int_0^1 v^{m-1}f(v^2s)p(v^2s)^{-\gamma}\,dv\right)^{1/m}$." (The recorded entry omits the defining average and gives only the value range as its space. The derivative interpretation applies to the fixed point, whereas the average is defined for every trial pair.)
- note on `symbol u`: symbol table corrected: space "$C^\infty(\mathcal U;\R)$, where $\mathcal U\subset\R^n$ is open" (The recorded space requires an entire function in every occurrence, whereas the reduction constructs a function on $\Omega\times\R$. The explicit ansatz and its entire radial specialization must be read in their respective scopes.)

### V1 lint warnings

- thm:main: thm:main references \ref{prop:reduction} (prop:reduction) but `depends_on` lacks ass:reduction-functions, ass:reduction-hessian, ass:reduction-system; V1.5 must confirm whether the paper assumes it or merely mentions it

### Parser warnings

- main.tex:9: \input{glyphtounicode} not found (tried glyphtounicode.tex, glyphtounicode relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)
- main.tex:10: \input{glyphtounicode-cmex} not found (tried glyphtounicode-cmex.tex, glyphtounicode-cmex relative to . and the source root); skipped (the bundle does not ship it — check that no result lived there)

## Lean evidence

- build of the run barrel: **ok**
- source scan (sorry / admit / axiom): clean

| declaration | axioms |
| --- | --- |
| `OaiSmoothNonquadraticAffine.exists_nonquadratic_entire_affine_maximal` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiSmoothNonquadraticAffine.reduction_affineMaximal` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiSmoothNonquadraticAffine.exists_local_radial_solution` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiSmoothNonquadraticAffine.autonomous_system_of_continuation` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiSmoothNonquadraticAffine.box_forward_invariant` | clean — `propext`, `Classical.choice`, `Quot.sound` |
| `OaiSmoothNonquadraticAffine.local_radial_solution_extends_globally` | clean — `propext`, `Classical.choice`, `Quot.sound` |

## Inputs

| artifact | status |
| --- | --- |
| `discovery/v1_scope.json` | present (6 environment(s)) |
| `discovery/v1_5_review.json` | present (verdict PASS) |
| `formalization/crosswalk_full.json` | present (295 object(s)) |
| `graph.json` | present (297 node(s)) |
| Lean evidence | collected (build ok, 0 scan issue(s), 294 declaration(s)) |

## Annotated paper

Annotated paper: `annotated/main.tex` (30 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`

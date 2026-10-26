# The corrected paper and its Lean formalization — oai_sharp_threshold_monotone

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:threshold} For every integer $n\ge2$, every nontrivial increasing family $\mathcal P$ of graphs on $n$ vertices invariant under all vertex permutations, and every $0<\varepsilon<1/2$, \begin{equation} \label{eq:threshold} p_{1-\varepsilon}(\mathcal P)-p_\varepsilon(\mathcal P) \le \frac{2^{19}}{(\log n)^2}\log\frac1{2\varepsilon}. \end{equation}

**Lean.** `Papers.OaiSharpThresholdMonotone.propertyQuantile_width_le` — `lean/Papers/OaiSharpThresholdMonotone/TThreshold.lean:48`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every integer $n\ge2$, every nontrivial increasing family $\mathcal P$ of graphs on $n$ vertices invariant under all vertex permutations, | `n : ℕ`<br>`P : Set (GraphEdge n → Bool)`<br>`hn : ThresholdVertexCount n`<br>`hP : ThresholdProperty P` |
| and every $0<\varepsilon<1/2$, | `ε : ℝ`<br>`hε : ThresholdEpsilon ε` |
| \begin{equation} p_{1-\varepsilon}(\mathcal P)-p_\varepsilon(\mathcal P) \le \frac{2^{19}}{(\log n)^2}\log\frac1{2\varepsilon}. \end{equation} | then `propertyQuantile (1 - ε) P - propertyQuantile ε P ≤ 2 ^ 19 / (Real.log n) ^ 2 * Real.log (1 / (2 * ε))` |

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For an integer $n\ge2$, write $[n]=\{1,\ldots,n\}$ and let $E_n=\binom{[n]}2$ be the edge set of the complete simple graph on $n$ vertices. → `GraphEdge` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:273`)
- definition of the paper: A \emph{graph property} is a family $\mathcal P\subseteq\{0,1\}^{E_n}$ invariant under every permutation of $[n]$. → `IsGraphProperty` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:315`)
- definition of the paper: It is \emph{increasing}, or \emph{monotone}, if adding edges preserves membership → `IsIncreasingGraphProperty` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:322`)
- definition of the paper: and \emph{nontrivial} if it is neither empty nor the whole space. → `IsNontrivialGraphProperty` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:331`)
- definition of the paper: Write $\mu_p(\mathcal P)$ for the probability that a graph whose edges are present independently with probability $p$ belongs to $\mathcal P$. → `propertyProb` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:551`)
- definition of the paper: For $0<a<1$, define \[ p_a(\mathcal P)=\inf\{p\in[0,1]:\mu_p(\mathcal P)\ge a\}. \] → `propertyQuantile` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:577`)
- definition of the paper: Here $x_{e\leftarrow b}$ denotes $x$ with coordinate $e$ set to $b\in\{0,1\}$ → `coordinateReplace` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:74`)
- definition of the paper: \[ I_{e,p}(f)=\Pr_p\bigl(f(x_{e\leftarrow1})\ne f(x_{e\leftarrow0})\bigr), \qquad I_p(f)=\sum_{e\in E_n}I_{e,p}(f). \] → `graphTotalInfluence` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:365`)
- condition of the paper: All logarithms in this paper are natural. → `NaturalLogarithms` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:68`)
- condition of the paper: For every integer $n\ge2$ → `ThresholdVertexCount` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:585`)
- condition of the paper: every nontrivial increasing family $\mathcal P$ of graphs on $n$ vertices invariant under all vertex permutations → `ThresholdProperty` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:592`)
- condition of the paper: every $0<\varepsilon<1/2$ → `ThresholdEpsilon` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:600`)
- definition of the paper: We identify a graph with an element of $\{0,1\}^{E_n}$. → `GraphConfig` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:280`)

## Theorem 1.2

**Statement.** \label{thm:variance} For every integer $n\ge2$, every Boolean function $f$ on $E_n$ invariant under vertex permutations, and every $0<p<1$, \begin{equation} \label{eq:variance} \Var_p(f)\le\frac{2^{17}}{(\log n)^2}I_p(f). \end{equation} No monotonicity assumption is needed.

**Lean.** `Papers.OaiSharpThresholdMonotone.variance_le_log_sq_inv_mul_totalInfluence` — `lean/Papers/OaiSharpThresholdMonotone/TVariance.lean:18`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every integer $n\ge2$, every Boolean function $f$ on $E_n$ invariant under vertex permutations, | `n : ℕ`<br>`f : (GraphEdge n → Bool) → Bool`<br>`hn : VarianceVertexCount n`<br>`hf : VarianceSymmetric f` |
| and every $0<p<1$, | `p : ℝ`<br>`hp : VarianceBias p` |
| \begin{equation} \Var_p(f)\le\frac{2^{17}}{(\log n)^2}I_p(f). \end{equation} | then `graphVariance p f ≤ 2 ^ 17 / (Real.log n) ^ 2 * graphTotalInfluence p f` |
| No monotonicity assumption is needed. | — (no Lean counterpart recorded) |

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For an integer $n\ge2$, write $[n]=\{1,\ldots,n\}$ and let $E_n=\binom{[n]}2$ be the edge set of the complete simple graph on $n$ vertices. → `GraphEdge` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:273`)
- condition of the paper: For every integer $n\ge2$ → `VarianceVertexCount` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:388`)
- condition of the paper: every Boolean function $f$ on $E_n$ invariant under vertex permutations → `VarianceSymmetric` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:394`)
- condition of the paper: every $0<p<1$ → `VarianceBias` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:399`)
- definition of the paper: let $0<p<1$, and put $\sigma=\sqrt{p(1-p)}$. → `biasScale` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:82`)
- definition of the paper: All Fourier coefficients, variances, and influences in this section use this bias. → `graphVariance` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:373`)
- condition of the paper: All logarithms in this paper are natural. → `NaturalLogarithms` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:68`)
- definition of the paper: Define \[ \chi_i(x)=\frac{x_i-p}{\sigma},\qquad \chi_S(x)=\prod_{i\in S}\chi_i(x),\qquad \chi_\varnothing=1. \] → `fourierChar` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:104`)
- definition of the paper: with $\widehat g(S)=\E[g\chi_S]$ → `fourierCoeffR` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:112`)
- definition of the paper: \begin{equation}\label{eq:parseval} g=\sum_{S\subseteq J}\widehat g(S)\chi_S,\qquad \E g^2=\sum_{S\subseteq J}\widehat g(S)^2,\qquad \Var(g)=\sum_{\varnothing\ne S\subseteq J}\widehat g(S)^2. \end{equation} → `fourierIdentities` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:136`)
- definition of the paper: For Boolean $h:\{0,1\}^J\to\{0,1\}$, set \[ I_i(h)=\Pr(\Delta_i h\ne0),\qquad I(h)=\sum_{i\in J}I_i(h). \] → `totalCoordInfluence` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:186`)
- definition of the paper: \[ I_{e,p}(f)=\Pr_p\bigl(f(x_{e\leftarrow1})\ne f(x_{e\leftarrow0})\bigr), \qquad I_p(f)=\sum_{e\in E_n}I_{e,p}(f). \] → `graphTotalInfluence` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:365`)
- definition of the paper: \begin{equation}\label{eq:dirichlet} \sum_{S\ni i}\widehat h(S)^2=\sigma^2 I_i(h),\qquad \sum_{S\subseteq J}|S|\widehat h(S)^2=\sigma^2 I(h). \end{equation} → `fourierInfluenceIdentities` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:207`)
- definition of the paper: put \[ m=\lfloor\sqrt n\rfloor, \qquad k=\frac{\sigma\log m}{64}. \] → `captureParameters` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:528`)
- definition of the paper: We identify a graph with an element of $\{0,1\}^{E_n}$. → `GraphConfig` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:280`)

## Lemma 2.1

**Statement.** \label{lem:low-degree} Let $m\ge2$ be real and let $h:\{0,1\}^J\to\{0,1\}$ satisfy $I_i(h)\le I(h)/m$ for every $i\in J$. If \[ k=\frac{\sigma\log m}{64}, \] then \begin{equation}\label{eq:low-degree} \sum_{1\le |S|\le k}\widehat h(S)^2\le m^{-1/4}I(h). \end{equation} Every degree cutoff is interpreted literally for integer degrees $|S|$; in particular, the sum is empty when $k<1$.

**Lean.** `Papers.OaiSharpThresholdMonotone.sum_lowDegree_fourierCoeff_sq_le` — `lean/Papers/OaiSharpThresholdMonotone/Helpers/LowDegree.lean:215`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $m\ge2$ be real and let $h:\{0,1\}^J\to\{0,1\}$ satisfy $I_i(h)\le I(h)/m$ for every $i\in J$. | `p m k : ℝ`<br>`h : (J → Bool) → Bool`<br>`hm : LowDegreeParam m`<br>`hsmall : SmallIndividualInfluences p h m` |
| If \[ k=\frac{\sigma\log m}{64}, \] | `p m k : ℝ`<br>`hk : LowDegreeCutoff p m k` |
| then \begin{equation} \sum_{1\le \|S\|\le k}\widehat h(S)^2\le m^{-1/4}I(h). \end{equation} | then `∑ S ∈ Finset.univ.filter (fun S : Finset J => 1 ≤ S.card ∧ (S.card : ℝ) ≤ k), fourierCoeff p h S ^ 2 ≤ m ^ (-(1 / 4 : ℝ)) * totalCoordInfluence p h` |
| Every degree cutoff is interpreted literally for integer degrees $\|S\|$; | — (no Lean counterpart recorded) |
| in particular, the sum is empty when $k<1$. | — (no Lean counterpart recorded) |

Lean also declares what the paper leaves implicit (the objects and their types): `J : Type*`, `Fintype J`, `DecidableEq J`.

Lean assumes conditions that the paper's text does not state: `hJ : FiniteCoordinateSet J`, `hp : BiasInterior p`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: Let $J$ be a finite coordinate set → `FiniteCoordinateSet` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:49`)
- condition of the paper: let $0<p<1$ → `BiasInterior` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:59`)
- definition of the paper: let $0<p<1$, and put $\sigma=\sqrt{p(1-p)}$. → `biasScale` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:82`)
- definition of the paper: in particular, $\|g\|_q=(\E|g|^q)^{1/q}$. → `cubeNorm` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:89`)
- definition of the paper: Define \[ \chi_i(x)=\frac{x_i-p}{\sigma},\qquad \chi_S(x)=\prod_{i\in S}\chi_i(x),\qquad \chi_\varnothing=1. \] → `fourierChar` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:104`)
- definition of the paper: with $\widehat g(S)=\E[g\chi_S]$ → `fourierCoeffR` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:112`)
- definition of the paper: \begin{equation}\label{eq:parseval} g=\sum_{S\subseteq J}\widehat g(S)\chi_S,\qquad \E g^2=\sum_{S\subseteq J}\widehat g(S)^2,\qquad \Var(g)=\sum_{\varnothing\ne S\subseteq J}\widehat g(S)^2. \end{equation} → `fourierIdentities` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:136`)
- definition of the paper: For $i\in J$, write $\Delta_i g(x)=g(x_{J\setminus\{i\}},1)-g(x_{J\setminus\{i\}},0)$, a function on the remaining coordinates. → `coordDiffR` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:150`)
- definition of the paper: For Boolean $h:\{0,1\}^J\to\{0,1\}$, set \[ I_i(h)=\Pr(\Delta_i h\ne0),\qquad I(h)=\sum_{i\in J}I_i(h). \] → `totalCoordInfluence` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:186`)
- condition of the paper: All logarithms in this paper are natural. → `NaturalLogarithms` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:68`)
- condition of the paper: Let $m\ge2$ be real → `LowDegreeParam` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:215`)
- condition of the paper: let $h:\{0,1\}^J\to\{0,1\}$ satisfy $I_i(h)\le I(h)/m$ for every $i\in J$. → `SmallIndividualInfluences` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:222`)
- condition of the paper: If \[ k=\frac{\sigma\log m}{64}, \] → `LowDegreeCutoff` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:235`)
- definition of the paper: Put $\rho=\sigma/4$ → `noiseParameter` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:241`)
- definition of the paper: define the linear operator $T_\rho$ by $T_\rho\chi_S=\rho^{|S|}\chi_S$. → `noiseOperator` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:249`)
- definition of the paper: For any real $d\ge0$, let $P_{\le d}$ be the orthogonal projection onto the span of the characters of degree at most $d$. → `lowProjection` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:262`)

## Lemma 3.1

**Statement.** \label{lem:restriction} Let $F\subseteq E_n$, put $H=E_n\setminus F$, and, for $y\in\{0,1\}^{H}$, let $f_y(x)=f(x,y)$ for $x\in\{0,1\}^{F}$. If $y$ has the Bernoulli-$p$ product law, then, for every real $k>0$, \begin{align} \E_y\sum_{\substack{A\subseteq F\\1\le |A|\le k}} \widehat{f_y}(A)^2 &=\sum_{\substack{S\subseteq E_n\\1\le|S\cap F|\le k}} \widehat f(S)^2, \label{eq:restriction-mass}\\ \E_y I(f_y)&=\sum_{e\in F}I_e(f). \label{eq:restriction-influence} \end{align}

**Lean.** `Papers.OaiSharpThresholdMonotone.restriction_mass_and_influence` — `lean/Papers/OaiSharpThresholdMonotone/Helpers/Restriction.lean:233`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $F\subseteq E_n$, put $H=E_n\setminus F$, | `F : Finset (GraphEdge n)`<br>`hF : FreeEdgeSet F` |
| and, for $y\in\{0,1\}^{H}$, let $f_y(x)=f(x,y)$ for $x\in\{0,1\}^{F}$. | — (no Lean counterpart recorded) |
| If $y$ has the Bernoulli-$p$ product law, | `p k : ℝ`<br>`ν : FiniteDesign ({e // e ∉ F} → Bool)`<br>`hν : ExteriorBernoulliLaw F p ν` |
| then, for every real $k>0$, | `p k : ℝ`<br>`hk : PositiveCutoff k` |
| \begin{align} \E_y\sum_{\substack{A\subseteq F\\1\le \|A\|\le k}} \widehat{f_y}(A)^2 &=\sum_{\substack{S\subseteq E_n\\1\le\|S\cap F\|\le k}} \widehat f(S)^2, \\ | then `ν.E (fun y => ∑ A ∈ Finset.univ.filter (fun A : Finset {e // e ∈ F} => 1 ≤ A.card ∧ (A.card : ℝ) ≤ k), fourierCoeff p (restrictFn f F y) A ^ 2) = ∑ S ∈ Finset.univ.filter (fun S : Finset (GraphEdge n) => 1 ≤ (S ∩ F).card ∧ ((S ∩ F).card : ℝ) ≤ k), graphFourierCoeff p f S ^ 2` |
| \E_y I(f_y)&=\sum_{e\in F}I_e(f). \end{align} | then `ν.E (fun y => totalCoordInfluence p (restrictFn f F y)) = ∑ e ∈ F, edgeInfluence p f e` |

Lean also declares what the paper leaves implicit (the objects and their types): `n : ℕ`, `f : GraphConfig n → Bool`.

Lean assumes conditions that the paper's text does not state: `hp : BiasInterior p`, `hf : BooleanGraphFunction f`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For an integer $n\ge2$, write $[n]=\{1,\ldots,n\}$ and let $E_n=\binom{[n]}2$ be the edge set of the complete simple graph on $n$ vertices. → `GraphEdge` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:273`)
- condition of the paper: let $0<p<1$ → `BiasInterior` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:59`)
- definition of the paper: let $0<p<1$, and put $\sigma=\sqrt{p(1-p)}$. → `biasScale` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:82`)
- definition of the paper: All Fourier coefficients, variances, and influences in this section use this bias. → `graphVariance` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:373`)
- condition of the paper: every Boolean f → `BooleanGraphFunction` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:347`)
- definition of the paper: Define \[ \chi_i(x)=\frac{x_i-p}{\sigma},\qquad \chi_S(x)=\prod_{i\in S}\chi_i(x),\qquad \chi_\varnothing=1. \] → `fourierChar` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:104`)
- definition of the paper: with $\widehat g(S)=\E[g\chi_S]$ → `fourierCoeffR` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:112`)
- definition of the paper: \begin{equation}\label{eq:parseval} g=\sum_{S\subseteq J}\widehat g(S)\chi_S,\qquad \E g^2=\sum_{S\subseteq J}\widehat g(S)^2,\qquad \Var(g)=\sum_{\varnothing\ne S\subseteq J}\widehat g(S)^2. \end{equation} → `fourierIdentities` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:136`)
- definition of the paper: \[ I_{e,p}(f)=\Pr_p\bigl(f(x_{e\leftarrow1})\ne f(x_{e\leftarrow0})\bigr), \qquad I_p(f)=\sum_{e\in E_n}I_{e,p}(f). \] → `graphTotalInfluence` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:365`)
- definition of the paper: For Boolean $h:\{0,1\}^J\to\{0,1\}$, set \[ I_i(h)=\Pr(\Delta_i h\ne0),\qquad I(h)=\sum_{i\in J}I_i(h). \] → `totalCoordInfluence` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:186`)
- condition of the paper: Let $F\subseteq E_n$ → `FreeEdgeSet` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:405`)
- definition of the paper: put $H=E_n\setminus F$ → `exteriorEdges` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:411`)
- definition of the paper: for $y\in\{0,1\}^{H}$, let $f_y(x)=f(x,y)$ for $x\in\{0,1\}^{F}$. → `restrictFn` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:427`)
- condition of the paper: If $y$ has the Bernoulli-$p$ product law → `ExteriorBernoulliLaw` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:464`)
- condition of the paper: for every real $k>0$ → `PositiveCutoff` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:471`)
- definition of the paper: We identify a graph with an element of $\{0,1\}^{E_n}$. → `GraphConfig` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:280`)

## Proposition 3.2

**Statement.** \label{prop:block} Let $3\le m\le n$ be an integer, let $B$ be uniform among the $m$-element subsets of $[n]$, and set \[ F_B=\{e\in E_n:e\cap B\ne\varnothing\}, \qquad k=\frac{\sigma\log m}{64}. \] Then \begin{equation} \sum_{S\subseteq E_n} \Pr_B\{1\le |S\cap F_B|\le k\}\widehat f(S)^2 \le \frac{2m}{n}\,m^{-1/4}I(f). \label{eq:block-average} \end{equation}

**Lean.** `Papers.OaiSharpThresholdMonotone.block_average_lowDegree_mass_le` — `lean/Papers/OaiSharpThresholdMonotone/Helpers/BlockAverage.lean:150`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $3\le m\le n$ be an integer, let $B$ be uniform among the $m$-element subsets of $[n]$, | `n m : ℕ`<br>`π : FiniteDesign {B : Finset (Fin n) // B.card = m}`<br>`hm : BlockSize m n`<br>`hπ : UniformBlockLaw n m π` |
| and set \[ F_B=\{e\in E_n:e\cap B\ne\varnothing\}, \qquad | — (no Lean counterpart recorded) |
| k=\frac{\sigma\log m}{64}. \] | — (no Lean counterpart recorded) |
| Then \begin{equation} \sum_{S\subseteq E_n} \Pr_B\{1\le \|S\cap F_B\|\le k\}\widehat f(S)^2 \le \frac{2m}{n}\,m^{-1/4}I(f). \end{equation} | then `∑ S : Finset (GraphEdge n), π.Pr (fun B => 1 ≤ (S ∩ freeEdges B.val).card ∧ ((S ∩ freeEdges B.val).card : ℝ) ≤ lowCutoff p m) * graphFourierCoeff p f S ^ 2 ≤ 2 * (m : ℝ) / n * (m : ℝ) ^ (-(1 / 4 : ℝ)) * graphTotalInfluence p f` |

Lean also declares what the paper leaves implicit (the objects and their types): `p : ℝ`, `f : GraphConfig n → Bool`.

Lean assumes conditions that the paper's text does not state: `hp : BiasInterior p`, `hf : GraphSymmetric f`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For an integer $n\ge2$, write $[n]=\{1,\ldots,n\}$ and let $E_n=\binom{[n]}2$ be the edge set of the complete simple graph on $n$ vertices. → `GraphEdge` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:273`)
- condition of the paper: let $0<p<1$ → `BiasInterior` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:59`)
- definition of the paper: let $0<p<1$, and put $\sigma=\sqrt{p(1-p)}$. → `biasScale` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:82`)
- definition of the paper: All Fourier coefficients, variances, and influences in this section use this bias. → `graphVariance` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:373`)
- condition of the paper: All logarithms in this paper are natural. → `NaturalLogarithms` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:68`)
- condition of the paper: and let $f\colon\{0,1\}^{E_n}\to\{0,1\}$ be invariant under vertex permutations. → `GraphSymmetric` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:339`)
- definition of the paper: \[ I_{e,p}(f)=\Pr_p\bigl(f(x_{e\leftarrow1})\ne f(x_{e\leftarrow0})\bigr), \qquad I_p(f)=\sum_{e\in E_n}I_{e,p}(f). \] → `graphTotalInfluence` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:365`)
- definition of the paper: For Boolean $h:\{0,1\}^J\to\{0,1\}$, set \[ I_i(h)=\Pr(\Delta_i h\ne0),\qquad I(h)=\sum_{i\in J}I_i(h). \] → `totalCoordInfluence` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:186`)
- definition of the paper: Define \[ \chi_i(x)=\frac{x_i-p}{\sigma},\qquad \chi_S(x)=\prod_{i\in S}\chi_i(x),\qquad \chi_\varnothing=1. \] → `fourierChar` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:104`)
- definition of the paper: with $\widehat g(S)=\E[g\chi_S]$ → `fourierCoeffR` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:112`)
- condition of the paper: Let $3\le m\le n$ be an integer → `BlockSize` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:480`)
- condition of the paper: let $B$ be uniform among the $m$-element subsets of $[n]$ → `UniformBlockLaw` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:487`)
- definition of the paper: set \[ F_B=\{e\in E_n:e\cap B\ne\varnothing\}, \qquad k=\frac{\sigma\log m}{64}. \] → `blockParameters` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:510`)
- definition of the paper: We identify a graph with an element of $\{0,1\}^{E_n}$. → `GraphConfig` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:280`)

## Lemma 3.3

**Statement.** \label{lem:block-capture} Suppose $t=\log n\ge16$, and put \[ m=\lfloor\sqrt n\rfloor, \qquad k=\frac{\sigma\log m}{64}. \] Then \begin{equation} \sum_{\substack{S\subseteq E_n\\1\le |S|\le k^2/2}} \widehat f(S)^2 \le 4m^{-1/4}I(f). \label{eq:captured-mass} \end{equation}

**Lean.** `Papers.OaiSharpThresholdMonotone.captured_lowDegree_mass_le` — `lean/Papers/OaiSharpThresholdMonotone/Helpers/BlockCapture.lean:19`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Suppose $t=\log n\ge16$, | `hn : CaptureLogSize n` |
| and put \[ m=\lfloor\sqrt n\rfloor, \qquad | — (no Lean counterpart recorded) |
| k=\frac{\sigma\log m}{64}. \] | — (no Lean counterpart recorded) |
| Then \begin{equation} \sum_{\substack{S\subseteq E_n\\1\le \|S\|\le k^2/2}} \widehat f(S)^2 \le 4m^{-1/4}I(f). \end{equation} | then `∑ S ∈ Finset.univ.filter (fun S : Finset (GraphEdge n) => 1 ≤ S.card ∧ (S.card : ℝ) ≤ lowCutoff p (sqrtBlockSize n) ^ 2 / 2), graphFourierCoeff p f S ^ 2 ≤ 4 * (sqrtBlockSize n : ℝ) ^ (-(1 / 4 : ℝ)) * graphTotalInfluence p f` |

Lean also declares what the paper leaves implicit (the objects and their types): `n : ℕ`, `p : ℝ`, `f : GraphConfig n → Bool`.

Lean assumes conditions that the paper's text does not state: `hp : BiasInterior p`, `hf : GraphSymmetric f`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For an integer $n\ge2$, write $[n]=\{1,\ldots,n\}$ and let $E_n=\binom{[n]}2$ be the edge set of the complete simple graph on $n$ vertices. → `GraphEdge` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:273`)
- condition of the paper: let $0<p<1$ → `BiasInterior` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:59`)
- definition of the paper: let $0<p<1$, and put $\sigma=\sqrt{p(1-p)}$. → `biasScale` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:82`)
- definition of the paper: All Fourier coefficients, variances, and influences in this section use this bias. → `graphVariance` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:373`)
- condition of the paper: All logarithms in this paper are natural. → `NaturalLogarithms` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:68`)
- condition of the paper: and let $f\colon\{0,1\}^{E_n}\to\{0,1\}$ be invariant under vertex permutations. → `GraphSymmetric` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:339`)
- definition of the paper: Define \[ \chi_i(x)=\frac{x_i-p}{\sigma},\qquad \chi_S(x)=\prod_{i\in S}\chi_i(x),\qquad \chi_\varnothing=1. \] → `fourierChar` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:104`)
- definition of the paper: with $\widehat g(S)=\E[g\chi_S]$ → `fourierCoeffR` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:112`)
- definition of the paper: \[ I_{e,p}(f)=\Pr_p\bigl(f(x_{e\leftarrow1})\ne f(x_{e\leftarrow0})\bigr), \qquad I_p(f)=\sum_{e\in E_n}I_{e,p}(f). \] → `graphTotalInfluence` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:365`)
- condition of the paper: Suppose $t=\log n\ge16$ → `CaptureLogSize` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:535`)
- definition of the paper: put \[ m=\lfloor\sqrt n\rfloor, \qquad k=\frac{\sigma\log m}{64}. \] → `captureParameters` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:528`)
- definition of the paper: set \[ F_B=\{e\in E_n:e\cap B\ne\varnothing\}, \qquad k=\frac{\sigma\log m}{64}. \] → `blockParameters` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:510`)
- definition of the paper: We identify a graph with an element of $\{0,1\}^{E_n}$. → `GraphConfig` (`lean/Papers/OaiSharpThresholdMonotone/Basic.lean:280`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:threshold` | `thm:threshold` | `sections/introduction.tex:12-20` | `Papers.OaiSharpThresholdMonotone.propertyQuantile_width_le` |
| Theorem 1.2 | `thm:variance` | `thm:variance` | `sections/introduction.tex:70-78` | `Papers.OaiSharpThresholdMonotone.variance_le_log_sq_inv_mul_totalInfluence` |
| Lemma 2.1 | `lem:low-degree` | `lem:low-degree` | `sections/fourier.tex:58-70` | `Papers.OaiSharpThresholdMonotone.sum_lowDegree_fourierCoeff_sq_le` |
| Lemma 3.1 | `lem:restriction` | `lem:restriction` | `sections/graph.tex:25-40` | `Papers.OaiSharpThresholdMonotone.restriction_mass_and_influence` |
| Proposition 3.2 | `prop:block` | `prop:block` | `sections/graph.tex:62-77` | `Papers.OaiSharpThresholdMonotone.block_average_lowDegree_mass_le` |
| Lemma 3.3 | `lem:block-capture` | `lem:block-capture` | `sections/graph.tex:111-125` | `Papers.OaiSharpThresholdMonotone.captured_lowDegree_mass_le` |

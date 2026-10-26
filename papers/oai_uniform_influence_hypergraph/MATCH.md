# The corrected paper and its Lean formalization — oai_uniform_influence_hypergraph

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} For every integer $r\ge3$ there is a finite constant $C_r$ such that, for every integer $n\ge r$, every $0<p<1$, and every hypergraph property $f:\{0,1\}^{E_{n,r}}\to\{0,1\}$, \begin{equation}\label{eq:main} \Var_p(f)\le \frac{C_r}{(\log n)^{r/(r-1)}}I_p(f). \end{equation} No monotonicity assumption is required.

**Lean.** `Papers.OaiUniformInfluenceHypergraph.variance_le_div_log_pow_mul_totalInfluence` — `lean/Papers/OaiUniformInfluenceHypergraph/TMain.lean:201`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every integer $r\ge3$ there is a finite constant $C_r$ such that, for every integer $n\ge r$, every $0<p<1$, | ≈ `r : ℕ`<br>≈ `MainUniformity r`<br>≈ then `∃ C : ℝ,`<br>≈ `n : ℕ`<br>≈ `MainVertexCount n r`<br>≈ `p : ℝ`<br>≈ `MainBias p`<br>≈ `BiasInterior p` |
| and every hypergraph property $f:\{0,1\}^{E_{n,r}}\to\{0,1\}$, | `f : (Edge n r → Bool) → Bool`<br>`IsHypergraphProperty f` |
| \begin{equation} \Var_p(f)\le \frac{C_r}{(\log n)^{r/(r-1)}}I_p(f). \end{equation} | then `(biasedLaw (Edge n r) p).Var (boolValue f) ≤ C / Real.log (n : ℝ) ^ captureExponent r * totalEdgeInfluence p f` |
| No monotonicity assumption is required. | — (no Lean counterpart recorded) |

A row marked ≈ was given these phrases with many rows of its result at once, not on its own.

Lean concludes what the paper's text does not state: `0 ≤ C`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: Let $r\ge3$ and $n\ge r$ be integers, write $[n]=\{1,\ldots,n\}$, and put $E_{n,r}=\binom{[n]}r$. → `Edge` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:98`)
- definition of the paper: A \emph{hypergraph property} is a Boolean function on this space that is invariant under every permutation of $[n]$. → `IsHypergraphProperty` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:110`)
- definition of the paper: For an edge $e$, let $x_{e\leftarrow b}$ be $x$ with its $e$-coordinate set to $b$. → `replaceCoord` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:119`)
- definition of the paper: Define the \emph{pivotal influence} of $e$ and the \emph{total influence} of $f$ by \[ I_{e,p}(f)=\Pr_p\bigl(f(x_{e\leftarrow1})\ne f(x_{e\leftarrow0})\bigr), \qquad I_p(f)=\sum_{e\in E_{n,r}}I_{e,p}(f). \] → `edgeInfluence` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:151`)
- definition of the paper: All logarithms are natural, and $n$ always counts vertices. → `natLog` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:164`)
- condition of the paper: For $0<p<1$, give the coordinates the independent Bernoulli$(p)$ law, → `BiasInterior` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:66`)
- definition of the paper: Fix $0<p<1$ and put $\sigma=\sqrt{p(1-p)}$. → `biasScale` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:207`)
- definition of the paper: For $i\in J$ and $A\subseteq J$, define \[ \chi_i(x)=\frac{x_i-p}{\sigma},\qquad \chi_A(x)=\prod_{i\in A}\chi_i(x),\qquad \chi_\varnothing=1. \] → `fourierChar` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:221`)
- definition of the paper: Write $\widehat h(A)=\E_p[h\chi_A]$. → `fourierCoeff` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:237`)
- definition of the paper: \begin{equation}\label{eq:parseval} \sum_{S\subseteq J}|S|\widehat h(S)^2=\sigma^2 I(h), \qquad \Var_p(h)=\sum_{\varnothing\ne S\subseteq J}\widehat h(S)^2. \end{equation} → `FourierIdentities` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:265`)
- definition of the paper: Return to a hypergraph property $f$ on $E=E_{n,r}$ and fix the bias $p$, with $\sigma=\sqrt{p(1-p)}$. Its Fourier coefficients use the basis of Section~\ref{sec:fourier}, with $J=E$. → `hyperFourierCoeff` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:283`)
- definition of the paper: For a vertex set $B\subseteq[n]$, write \[ F_B=\{e\in E:e\cap B\ne\varnothing\} \] for the edge coordinates that remain free. → `freeEdges` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:289`)
- definition of the paper: Combining Lemmas~\ref{lem:block} and~\ref{lem:capture} gives, whenever their hypotheses hold, \begin{equation}\label{eq:captured-mass} \sum_{1\le|S|\le L}\widehat f(S)^2 \le 2r m^{-1/4}I_p(f). \end{equation} → `CapturedMassEstimate` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:364`)
- condition of the paper: For every integer $r\ge3$ → `MainUniformity` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:77`)
- condition of the paper: for every integer $n\ge r$ → `MainVertexCount` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:82`)
- condition of the paper: every $0<p<1$ → `MainBias` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:87`)

## Lemma 2.1

**Statement.** \label{lem:low} Let $m\ge2$ be real and let $h:\{0,1\}^J\to\{0,1\}$ satisfy $I_i(h)\le I(h)/m$ for every $i\in J$. With $k=\sigma\log m/64$, one has \begin{equation}\label{eq:low} \sum_{1\le |S|\le k}\widehat h(S)^2\le m^{-1/4}I(h). \end{equation} The sum is empty when $k<1$.

**Lean.** `Papers.OaiUniformInfluenceHypergraph.sum_lowDegree_fourierCoeff_sq_le` — `lean/Papers/OaiUniformInfluenceHypergraph/Helpers/LowDegree.lean:196`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $m\ge2$ be real and let $h:\{0,1\}^J\to\{0,1\}$ satisfy $I_i(h)\le I(h)/m$ for every $i\in J$. | `p m : ℝ`<br>`h : (J → Bool) → Bool`<br>`hm : LowDegreeParam m`<br>`hI : SmallIndividualInfluences p h m` |
| With $k=\sigma\log m/64$, one has | — (no Lean counterpart recorded) |
| \begin{equation} \sum_{1\le \|S\|\le k}\widehat h(S)^2\le m^{-1/4}I(h). \end{equation} | then `(∑ S ∈ Finset.univ.filter (fun S : Finset J => 1 ≤ S.card ∧ (S.card : ℝ) ≤ lowCutoff p m), fourierCoeff p h S ^ 2) ≤ m ^ (-(1 : ℝ) / 4) * totalCoordInfluence p h` |
| The sum is empty when $k<1$. | — (no Lean counterpart recorded) |

Lean also declares what the paper leaves implicit (the objects and their types): `J : Type*`, `Fintype J`, `DecidableEq J`.

Lean assumes conditions that the paper's text does not state: `hp : BiasInterior p`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: For $0<p<1$, give the coordinates the independent Bernoulli$(p)$ law, → `BiasInterior` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:66`)
- condition of the paper: Let $m\ge2$ be real → `LowDegreeParam` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:72`)
- condition of the paper: let $h:\{0,1\}^J\to\{0,1\}$ satisfy $I_i(h)\le I(h)/m$ for every $i\in J$. → `SmallIndividualInfluences` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:143`)
- definition of the paper: Fix $0<p<1$ and put $\sigma=\sqrt{p(1-p)}$. → `biasScale` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:207`)
- definition of the paper: Define the \emph{pivotal influence} of $e$ and the \emph{total influence} of $f$ by \[ I_{e,p}(f)=\Pr_p\bigl(f(x_{e\leftarrow1})\ne f(x_{e\leftarrow0})\bigr), \qquad I_p(f)=\sum_{e\in E_{n,r}}I_{e,p}(f). \] → `edgeInfluence` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:151`)
- definition of the paper: For $i\in J$ and $A\subseteq J$, define \[ \chi_i(x)=\frac{x_i-p}{\sigma},\qquad \chi_A(x)=\prod_{i\in A}\chi_i(x),\qquad \chi_\varnothing=1. \] → `fourierChar` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:221`)
- definition of the paper: Write $\widehat h(A)=\E_p[h\chi_A]$. → `fourierCoeff` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:237`)
- definition of the paper: For Boolean $h$, let $\Delta_i h$ be the function on the other coordinates obtained by subtracting the section at $x_i=0$ from the section at $x_i=1$. → `coordDiff` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:247`)
- definition of the paper: \begin{equation}\label{eq:parseval} \sum_{S\subseteq J}|S|\widehat h(S)^2=\sigma^2 I(h), \qquad \Var_p(h)=\sum_{\varnothing\ne S\subseteq J}\widehat h(S)^2. \end{equation} → `FourierIdentities` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:265`)
- definition of the paper: With $k=\sigma\log m/64$ → `lowCutoff` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:276`)
- definition of the paper: All logarithms are natural, and $n$ always counts vertices. → `natLog` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:164`)
- definition of the paper: Throughout this section, norms and expectations use this product law, and $I_i(h)$ and $I(h)$ denote pivotal and total influence on $J$. → `coordInfluence` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:128`)

## Lemma 3.1

**Statement.** \label{lem:block} Let $r+1\le m\le n$ be integers and set $k=\sigma\log m/64$. For $B$ chosen uniformly among the $m$-subsets of $[n]$, \begin{equation}\label{eq:block} \sum_{S\subseteq E} \Pr_B(1\le|S\cap F_B|\le k)\widehat f(S)^2 \le m^{-1/4}\frac{rm}{n}I_p(f). \end{equation}

**Lean.** `Papers.OaiUniformInfluenceHypergraph.sum_blockProb_mul_fourierCoeff_sq_le` — `lean/Papers/OaiUniformInfluenceHypergraph/Helpers/Block.lean:164`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $r+1\le m\le n$ be integers and set $k=\sigma\log m/64$. | `r m n : ℕ`<br>`hdom : BlockDomain r m n`<br>then `(∑ S : Finset (Edge n r), blockCaptureProb n r m hdom.2 (blockCutoff p m) S * hyperFourierCoeff p f S ^ 2) ≤ (m : ℝ) ^ (-(1 : ℝ) / 4) * ((r : ℝ) * m / n) * totalEdgeInfluence p f` |
| For $B$ chosen uniformly among the $m$-subsets of $[n]$, | then `(∑ S : Finset (Edge n r), blockCaptureProb n r m hdom.2 (blockCutoff p m) S * hyperFourierCoeff p f S ^ 2) ≤ (m : ℝ) ^ (-(1 : ℝ) / 4) * ((r : ℝ) * m / n) * totalEdgeInfluence p f` |
| \begin{equation} \sum_{S\subseteq E} \Pr_B(1\le\|S\cap F_B\|\le k)\widehat f(S)^2 \le m^{-1/4}\frac{rm}{n}I_p(f). \end{equation} | then `(∑ S : Finset (Edge n r), blockCaptureProb n r m hdom.2 (blockCutoff p m) S * hyperFourierCoeff p f S ^ 2) ≤ (m : ℝ) ^ (-(1 : ℝ) / 4) * ((r : ℝ) * m / n) * totalEdgeInfluence p f` |

Lean also declares what the paper leaves implicit (the objects and their types): `p : ℝ`, `f : (Edge n r → Bool) → Bool`.

Lean assumes conditions that the paper's text does not state: `hp : BiasInterior p`, `hf : IsHypergraphProperty f`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: Let $r\ge3$ and $n\ge r$ be integers, write $[n]=\{1,\ldots,n\}$, and put $E_{n,r}=\binom{[n]}r$. → `Edge` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:98`)
- definition of the paper: A \emph{hypergraph property} is a Boolean function on this space that is invariant under every permutation of $[n]$. → `IsHypergraphProperty` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:110`)
- definition of the paper: For an edge $e$, let $x_{e\leftarrow b}$ be $x$ with its $e$-coordinate set to $b$. → `replaceCoord` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:119`)
- definition of the paper: Define the \emph{pivotal influence} of $e$ and the \emph{total influence} of $f$ by \[ I_{e,p}(f)=\Pr_p\bigl(f(x_{e\leftarrow1})\ne f(x_{e\leftarrow0})\bigr), \qquad I_p(f)=\sum_{e\in E_{n,r}}I_{e,p}(f). \] → `edgeInfluence` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:151`)
- definition of the paper: All logarithms are natural, and $n$ always counts vertices. → `natLog` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:164`)
- condition of the paper: For $0<p<1$, give the coordinates the independent Bernoulli$(p)$ law, → `BiasInterior` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:66`)
- definition of the paper: Fix $0<p<1$ and put $\sigma=\sqrt{p(1-p)}$. → `biasScale` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:207`)
- definition of the paper: For $i\in J$ and $A\subseteq J$, define \[ \chi_i(x)=\frac{x_i-p}{\sigma},\qquad \chi_A(x)=\prod_{i\in A}\chi_i(x),\qquad \chi_\varnothing=1. \] → `fourierChar` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:221`)
- definition of the paper: Write $\widehat h(A)=\E_p[h\chi_A]$. → `fourierCoeff` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:237`)
- condition of the paper: Let $r+1\le m\le n$ be integers → `BlockDomain` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:302`)
- definition of the paper: Return to a hypergraph property $f$ on $E=E_{n,r}$ and fix the bias $p$, with $\sigma=\sqrt{p(1-p)}$. Its Fourier coefficients use the basis of Section~\ref{sec:fourier}, with $J=E$. → `hyperFourierCoeff` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:283`)
- definition of the paper: For a vertex set $B\subseteq[n]$, write \[ F_B=\{e\in E:e\cap B\ne\varnothing\} \] for the edge coordinates that remain free. → `freeEdges` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:289`)
- definition of the paper: set $k=\sigma\log m/64$. → `blockCutoff` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:295`)

## Lemma 3.2

**Statement.** \label{lem:capture} Let $n\ge r\ge3$ and $1\le m\le n$ be integers, let $k>0$, and put \[ \alpha=\frac r{r-1},\qquad L=(k/r)^\alpha. \] Suppose \begin{equation}\label{eq:capture-condition} rL\frac{m-1}{n-1}\le\frac12. \end{equation} For a uniform $m$-subset $B$ of $[n]$ and every $S\subseteq E_{n,r}$ with $1\le|S|\le L$, \begin{equation}\label{eq:capture} \Pr_B(1\le|S\cap F_B|\le k)\ge\frac{m}{2n}. \end{equation}

**Lean.** `Papers.OaiUniformInfluenceHypergraph.blockProb_capture_ge` — `lean/Papers/OaiUniformInfluenceHypergraph/Helpers/Capture.lean:127`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $n\ge r\ge3$ | `n r m : ℕ`<br>`hd : CaptureDomain n r m` |
| and $1\le m\le n$ be integers, let $k>0$, | `n r m : ℕ`<br>`k : ℝ`<br>`hd : CaptureDomain n r m`<br>`hk : CapturePositiveCutoff k` |
| and put \[ \alpha=\frac r{r-1},\qquad | `hc : CaptureCondition r n m k`<br>`hS : CaptureSupport S (supportCutoff r k)` |
| L=(k/r)^\alpha. \] | `hc : CaptureCondition r n m k`<br>`hS : CaptureSupport S (supportCutoff r k)` |
| Suppose \begin{equation} rL\frac{m-1}{n-1}\le\frac12. \end{equation} | `hc : CaptureCondition r n m k` |
| For a uniform $m$-subset $B$ of $[n]$ and every $S\subseteq E_{n,r}$ with $1\le\|S\|\le L$, | `S : Finset (Edge n r)`<br>`hS : CaptureSupport S (supportCutoff r k)`<br>then `(m : ℝ) / (2 * n) ≤ blockCaptureProb n r m hd.2.2.2 k S` |
| \begin{equation} \Pr_B(1\le\|S\cap F_B\|\le k)\ge\frac{m}{2n}. \end{equation} | then `(m : ℝ) / (2 * n) ≤ blockCaptureProb n r m hd.2.2.2 k S` |

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: Let $r\ge3$ and $n\ge r$ be integers, write $[n]=\{1,\ldots,n\}$, and put $E_{n,r}=\binom{[n]}r$. → `Edge` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:98`)
- definition of the paper: For a vertex set $B\subseteq[n]$, write \[ F_B=\{e\in E:e\cap B\ne\varnothing\} \] for the edge coordinates that remain free. → `freeEdges` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:289`)
- definition of the paper: and put \[ \alpha=\frac r{r-1},\qquad L=(k/r)^\alpha. \] → `supportCutoff` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:325`)
- condition of the paper: Let $n\ge r\ge3$ and $1\le m\le n$ be integers → `CaptureDomain` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:310`)
- condition of the paper: let $k>0$ → `CapturePositiveCutoff` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:315`)
- condition of the paper: Suppose \begin{equation}\label{eq:capture-condition} rL\frac{m-1}{n-1}\le\frac12. \end{equation} → `CaptureCondition` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:333`)
- condition of the paper: every $S\subseteq E_{n,r}$ with $1\le|S|\le L$ → `CaptureSupport` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:340`)

## Corollary 4.1

**Statement.** \label{cor:threshold} For a nontrivial increasing property of $r$-uniform hypergraphs on $n\ge r$ vertices, where $r\ge3$, and every $0<\varepsilon<1/2$, \[ p_{1-\varepsilon}-p_\varepsilon \le\frac{2C_r}{(\log n)^{r/(r-1)}} \log\frac{1-\varepsilon}{\varepsilon}. \]

**Lean.** `Papers.OaiUniformInfluenceHypergraph.thresholdWidth_le` — `lean/Papers/OaiUniformInfluenceHypergraph/TCorThreshold.lean:18`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For a nontrivial increasing property of $r$-uniform hypergraphs on $n\ge r$ vertices, | `n : ℕ`<br>`MainVertexCount n r`<br>`f : (Edge n r → Bool) → Bool`<br>`IsHypergraphProperty f`<br>`IsIncreasingNontrivial f` |
| where $r\ge3$, | `r : ℕ`<br>`MainUniformity r` |
| and every $0<\varepsilon<1/2$, | `ε : ℝ`<br>`ThresholdEpsilon ε` |
| \[ p_{1-\varepsilon}-p_\varepsilon \le\frac{2C_r}{(\log n)^{r/(r-1)}} \log\frac{1-\varepsilon}{\varepsilon}. \] | then `thresholdWidth f ε ≤ 2 * C / Real.log (n : ℝ) ^ captureExponent r * Real.log ((1 - ε) / ε)` |

Lean also declares what the paper leaves implicit (the objects and their types): `C : ℝ`, `n : ℕ`, `p : ℝ`, `f : (Edge n r → Bool) → Bool`.

Lean assumes conditions that the paper's text does not state: `0 ≤ C`, `MainVertexCount n r`, `MainBias p`, `IsHypergraphProperty f`, `(biasedLaw (Edge n r) p).Var (boolValue f) ≤ C / Real.log (n : ℝ) ^ captureExponent r * totalEdgeInfluence p f`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: A property is \emph{increasing} if changing coordinates from $0$ to $1$ cannot decrease its value, and \emph{nontrivial} if it is not constant. → `IsIncreasingNontrivial` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:170`)
- definition of the paper: For a nontrivial increasing property, put $q(p)=\E_p f$ and define $p_a=\inf\{p\in[0,1]:q(p)\ge a\}$ for $0<a<1$. → `thresholdQuantile` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:187`)
- definition of the paper: For fixed $0<\varepsilon<1/2$, its \emph{threshold width} is $p_{1-\varepsilon}-p_\varepsilon$. → `thresholdWidth` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:194`)
- definition of the paper: Define the \emph{pivotal influence} of $e$ and the \emph{total influence} of $f$ by \[ I_{e,p}(f)=\Pr_p\bigl(f(x_{e\leftarrow1})\ne f(x_{e\leftarrow0})\bigr), \qquad I_p(f)=\sum_{e\in E_{n,r}}I_{e,p}(f). \] → `edgeInfluence` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:151`)
- definition of the paper: For an edge $e$, let $x_{e\leftarrow b}$ be $x$ with its $e$-coordinate set to $b$. → `replaceCoord` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:119`)
- definition of the paper: All logarithms are natural, and $n$ always counts vertices. → `natLog` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:164`)
- condition of the paper: For $0<p<1$, give the coordinates the independent Bernoulli$(p)$ law, → `BiasInterior` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:66`)
- condition of the paper: every $0<\varepsilon<1/2$ → `ThresholdEpsilon` (`lean/Papers/OaiUniformInfluenceHypergraph/Basic.lean:201`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `introduction.tex:24-32` | `Papers.OaiUniformInfluenceHypergraph.variance_le_div_log_pow_mul_totalInfluence` |
| Lemma 2.1 | `lem:low` | `lem:low` | `fourier.tex:39-47` | `Papers.OaiUniformInfluenceHypergraph.sum_lowDegree_fourierCoeff_sq_le` |
| Lemma 3.1 | `lem:block` | `lem:block` | `restriction.tex:18-26` | `Papers.OaiUniformInfluenceHypergraph.sum_blockProb_mul_fourierCoeff_sq_le` |
| Lemma 3.2 | `lem:capture` | `lem:capture` | `restriction.tex:72-86` | `Papers.OaiUniformInfluenceHypergraph.blockProb_capture_ge` |
| Corollary 4.1 | `thm:cor-threshold` | `cor:threshold` | `completion.tex:71-79` | `Papers.OaiUniformInfluenceHypergraph.thresholdWidth_le` |

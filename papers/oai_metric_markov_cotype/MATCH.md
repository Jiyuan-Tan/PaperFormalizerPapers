# The corrected paper and its Lean formalization — oai_metric_markov_cotype

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.2

**Statement.** \label{thm:main} The real space $\ell_1$ satisfies \[ N_2(\ell_1)\leq12\sqrt{21}. \]

**Lean.** `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_realEllOne_le` — `lean/Papers/OaiMetricMarkovCotype/TMain.lean:47`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| The real space $\ell_1$ satisfies | then `metricMarkovCotypeConstant RealEllOne ≤ ENNReal.ofReal (12 * Real.sqrt 21)` |
| \[ N_2(\ell_1)\leq12\sqrt{21}. \] | then `metricMarkovCotypeConstant RealEllOne ≤ ENNReal.ofReal (12 * Real.sqrt 21)` |

**Conditions and readings, and the Lean definitions that carry them.**

- reading: In the cost identities, $B=\sum_i\pi_i\|z_i-\Phi(h_i)\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. → `ApproxCostReading` (`lean/Papers/OaiMetricMarkovCotype/Helpers/StoppedWalk.lean:198`)
- definition of the paper: We work first with the real Banach space \[ \ell_1=\left\{x=(x(k))_{k\geq1}:\sum_{k\geq1}|x(k)|<\infty\right\}, \qquad \|x\|_1=\sum_{k\geq1}|x(k)|. \] → `RealEllOne` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:38`)
- definition of the paper: Write $\N=\{1,2,\ldots\}$ and $[n]=\{1,\ldots,n\}$. → `StateSet` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:52`)
- definition of the paper: A stochastic matrix $A=(a_{ij})_{i,j\in[n]}$ has nonnegative entries and each row sum equal to one. → `IsStochastic` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:88`)
- definition of the paper: It is reversible with respect to a probability vector $\pi=(\pi_i)_{i\in[n]}$ if $\pi_i a_{ij}=\pi_j a_{ji}$ for all $i,j$. → `IsReversible` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:96`)
- definition of the paper: \label{def:cotype} A metric space $(X,d)$ has metric Markov cotype two with constant $C>0$ if, for every $n,t\in\N$, every probability vector $\pi$, every stochastic matrix $A$ reversible with respect to $\pi$, and every $x_1,\ldots,x_n\in X$, there exist $y_1,\ldots,y_n\in X$ such that \begin{equation}\label{eq:cotype} \sum_i\pi_i d(x_i,y_i)^2 +t\sum_{i,j}\pi_i a_{ij}d(y_i,y_j)^2 \leq C^2\sum_{i,j}\pi_i \left(\frac1t\sum_{s=1}^t A^s\right)_{ij}d(x_i,x_j)^2. \end{equation} → `HasMetricMarkovCotypeTwo` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:137`)
- definition of the paper: The infimum of all such constants is denoted $N_2(X)$. → `metricMarkovCotypeConstant` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:145`)
- definition of the paper: We now construct the required points. Fix the data in Definition~\ref{def:cotype} with $X=\ell_1$. If all $x_i$ coincide, choose $y_i=x_i$. Otherwise use Lemma~\ref{lem:cuts} to obtain $z_i,H,T$, and use the map $\Phi$ of Section~\ref{sec:flat}. Put $p=1/(t+1)$, $q=1-p$, and define \begin{equation}\label{eq:resolvent} h_i=p\sum_{s=0}^\infty q^s(A^s z)_i, \qquad (A^s z)_i=\sum_j(A^s)_{ij}z_j. \end{equation} This convex combination converges in the finite-dimensional space $H$ and belongs to $Q$. Equivalently, $h_i=\E_i z_{X_S}$, where $\E_i$ refers to an $A$-walk started at $i$ and $S$ is independent with $\Prob(S=s)=pq^s$. The first-step identity is \begin{equation}\label{eq:harmonic} h_i=pz_i+q\sum_j a_{ij}h_j. \end{equation} We take \begin{equation}\label{eq:y} y_i=T(\Phi(h_i)). \end{equation} → `modifiedPoints` (`lean/Papers/OaiMetricMarkovCotype/Helpers/StoppedWalk.lean:42`)
- definition of the paper: Start a chain in an alive state with index distributed according to $\pi$. From an alive state of index $i$, it moves to the dead state of index $i$ with probability $p$, and to the alive state of index $j$ with probability $qa_{ij}$. Dead states are absorbing. Its filtration $\calF_m$ records the initial state and the first $m$ transitions only. One realization uses an independent stationary $A$-walk $(X_s)_{s\geq0}$ and successive independent survival trials, each successful with probability $q$. Let $S$ be the number of successful trials before the first failure. Then $\Prob(S=s)=pq^s$ and $S$ is independent of the walk. There are $S$ live index transitions followed by one death transition; the index at death is $X_S$. Attach the value $h_i$ to the alive state of index $i$ and the value $z_i$ to its dead state, and let $M_m$ be the attached value at chain time $m$. Equation~\eqref{eq:harmonic} shows that $(M_m)$ is an $H$-valued martingale for the indicated filtration. It lies in $Q$ and is eventually constant almost surely, with \[ M_0=h_{X_0},\qquad M_\infty=z_{X_S}. \] The vector $e=z_{X_0}$ is $\calF_0$-measurable and binary. Corollary~\ref{cor:martingale} and \eqref{eq:cut-distance} give \begin{equation}\label{eq:stopped-bound} \E\sum_{m=0}^\infty \|\Phi(M_{m+1})-\Phi(M_m)\|_{1,w}^2 \leq108\E\|x_{X_S}-x_{X_0}\|_1^2. \end{equation} To compute the left side exactly, set \[ B=\sum_i\pi_i\|z_i-\Phi(h_i)\|_{1,w}^2, \qquad E_A=\sum_{i,j}\pi_i a_{ij} \|\Phi(h_i)-\Phi(h_j)\|_{1,w}^2. \] At time $m$, the event that the chain is alive has probability $q^m$ and is independent of $X_m$. Stationarity gives $\Prob(X_m=i)=\pi_i$ and $\Prob(X_m=i,X_{m+1}=j)=\pi_i a_{ij}$. Since $\Phi(z_i)=z_i$, the expected squared jump at time $m$ is $pq^m B+q^{m+1}E_A$. Therefore \begin{equation}\label{eq:jump-identity} \E\sum_{m=0}^\infty \|\Phi(M_{m+1})-\Phi(M_m)\|_{1,w}^2 =B+\frac qp E_A=B+tE_A. \end{equation} → `stoppedWalkValue` (`lean/Papers/OaiMetricMarkovCotype/Helpers/StoppedWalk.lean:146`)

## Lemma 2.1

**Statement.** \label{lem:cuts} Given $x_1,\ldots,x_n\in\ell_1$, either all the points coincide, or there exist a finite set $\mathcal B$, positive weights $(w_B)_{B\in\mathcal B}$, binary vectors $z_i\in\{0,1\}^{\mathcal B}$, and an affine map $T:\R^{\mathcal B}\to\ell_1$ with the following properties. For \[ \|u\|_{1,w}=\sum_{B\in\mathcal B}w_B|u_B|, \qquad \|u\|_H^2=\sum_{B\in\mathcal B}w_Bu_B^2, \] one has \begin{align} T(z_i)&=x_i,\label{eq:reconstruct}\\ \|x_i-x_j\|_1 &=\|z_i-z_j\|_{1,w}=\|z_i-z_j\|_H^2, \label{eq:cut-distance}\\ \|T(u)-T(u')\|_1&\leq\|u-u'\|_{1,w} \qquad(u,u'\in\R^{\mathcal B}).\label{eq:contraction} \end{align} The space $H$ is $\R^{\mathcal B}$ with the indicated Hilbert norm.

**Lean.** `Papers.OaiMetricMarkovCotype.cut_decomposition` — `lean/Papers/OaiMetricMarkovCotype/Helpers/Cuts.lean:569`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Given $x_1,\ldots,x_n\in\ell_1$, either all the points coincide, or there exist a finite set $\mathcal B$, positive weights $(w_B)_{B\in\mathcal B}$, binary vectors $z_i\in\{0,1\}^{\mathcal B}$, | ≈ `x : Fin n → RealEllOne`<br>≈ `∀ i j`<br>≈ then `x i = x j`<br>≈ then `PositiveWeights (cutWeight x)`<br>≈ `∀ i`<br>≈ then `BinaryVector (cutEncoding x i)` |
| and an affine map $T:\R^{\mathcal B}\to\ell_1$ with the following properties. | `∀ (r : ℝ) u u'`<br>then `cutReconstruction x (r • u + (1 - r) • u') = r • cutReconstruction x u + (1 - r) • cutReconstruction x u'` |
| For \[ \\|u\\|_{1,w}=\sum_{B\in\mathcal B}w_B\|u_B\|, \qquad | — (no Lean counterpart recorded) |
| \\|u\\|_H^2=\sum_{B\in\mathcal B}w_Bu_B^2, \] | — (no Lean counterpart recorded) |
| one has \begin{align} T(z_i)&=x_i,\\ | `∀ i`<br>then `cutReconstruction x (cutEncoding x i) = x i` |
| \\|x_i-x_j\\|_1 &=\\|z_i-z_j\\|_{1,w}=\\|z_i-z_j\\|_H^2, \\ | `∀ i j`<br>then `‖x i - x j‖ = weightedL1Norm (cutWeight x) (cutEncoding x i - cutEncoding x j)`<br>then `weightedL1Norm (cutWeight x) (cutEncoding x i - cutEncoding x j) = weightedHNormSq (cutWeight x) (cutEncoding x i - cutEncoding x j)` |
| \\|T(u)-T(u')\\|_1&\leq\\|u-u'\\|_{1,w} \qquad | then `‖cutReconstruction x u - cutReconstruction x u'‖ ≤ weightedL1Norm (cutWeight x) (u - u')` |
| (u,u'\in\R^{\mathcal B}). \end{align} | `∀ u u'` |
| The space $H$ is $\R^{\mathcal B}$ with the indicated Hilbert norm. | — (no Lean counterpart recorded) |

A row marked ≈ was given these phrases with many rows of its result at once, not on its own.

Lean also declares what the paper leaves implicit (the objects and their types): `n : ℕ`.

Lean assumes conditions that the paper's text does not state: `h_data : CutsData n x`.

Lean concludes what the paper's text does not state: `Nonempty ↥(cutIndex x)`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: We work first with the real Banach space \[ \ell_1=\left\{x=(x(k))_{k\geq1}:\sum_{k\geq1}|x(k)|<\infty\right\}, \qquad \|x\|_1=\sum_{k\geq1}|x(k)|. \] → `RealEllOne` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:38`)
- definition of the paper: Write $\N=\{1,2,\ldots\}$ and $[n]=\{1,\ldots,n\}$. → `StateSet` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:52`)
- condition of the paper: Given $x_1,\ldots,x_n\in\ell_1$ → `CutsData` (`lean/Papers/OaiMetricMarkovCotype/Helpers/Cuts.lean:21`)

## Lemma 3.1

**Statement.** \label{lem:flat} For $u,u'\in Q$ and $e\in\{0,1\}^{\mathcal B}$, put $a=u-e$, $\delta=u'-u$, and $F_e(u)=\|u-e\|_H^4$. Then \begin{equation}\label{eq:flat} \|\Phi(u')-\Phi(u)\|_{1,w}^2 \leq108\bigl(F_e(u')-F_e(u) -4\|a\|_H^2\langle a,\delta\rangle_H\bigr). \end{equation}

**Lean.** `Papers.OaiMetricMarkovCotype.flat_cubic_bound` — `lean/Papers/OaiMetricMarkovCotype/Helpers/Flat.lean:161`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For $u,u'\in Q$ | `w u u' e : 𝓑 → ℝ`<br>`h_arguments : CubeArguments u u'` |
| and $e\in\{0,1\}^{\mathcal B}$, put $a=u-e$, | `w u u' e : 𝓑 → ℝ`<br>`h_center : BinaryVector e` |
| $\delta=u'-u$, | — (no Lean counterpart recorded) |
| and $F_e(u)=\\|u-e\\|_H^4$. | — (no Lean counterpart recorded) |
| Then \begin{equation} \\|\Phi(u')-\Phi(u)\\|_{1,w}^2 \leq108\bigl(F_e(u')-F_e(u) -4\\|a\\|_H^2\langle a,\delta\rangle_H\bigr). \end{equation} | then `weightedL1Norm w (cubicMap u' - cubicMap u) ^ 2 ≤ 108 * (quarticPotential w e u' - quarticPotential w e u - 4 * weightedHNormSq w (u - e) * weightedInner w (u - e) (u' - u))` |

Lean also declares what the paper leaves implicit (the objects and their types): `𝓑 : Type*`, `Fintype 𝓑`.

Lean assumes conditions that the paper's text does not state: `h_finite : FiniteCutIndex 𝓑`, `h_weights : PositiveWeights w`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For \[ \|u\|_{1,w}=\sum_{B\in\mathcal B}w_B|u_B|, \qquad \|u\|_H^2=\sum_{B\in\mathcal B}w_Bu_B^2, \] → `weightedL1Norm` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:171`)
- definition of the paper: The space $H$ is $\R^{\mathcal B}$ with the indicated Hilbert norm. → `weightedHNorm` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:185`)
- definition of the paper: Write $Q=[0,1]^{\mathcal B}$ and let $\langle\cdot,\cdot\rangle_H$ be the weighted Hilbert inner product. → `weightedInner` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:192`)
- definition of the paper: Define \[ \phi(r)=3r^2-2r^3\quad(0\leq r\leq1), \qquad \Phi(u)_B=\phi(u_B)\quad(u\in Q). \] → `cubicMap` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:256`)
- definition of the paper: put $a=u-e$, $\delta=u'-u$, and $F_e(u)=\|u-e\|_H^4$. → `quarticPotential` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:264`)
- condition of the paper: Fix a finite nonempty set $\mathcal B$ → `FiniteCutIndex` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:154`)
- condition of the paper: positive weights $w_B$ → `PositiveWeights` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:162`)
- condition of the paper: For $u,u'\in Q$ → `CubeArguments` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:212`)
- condition of the paper: $e\in\{0,1\}^{\mathcal B}$ → `BinaryVector` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:219`)

## Corollary 3.2

**Statement.** \label{cor:martingale} Let $(M_m)_{m\geq0}$ be an $H$-valued martingale with respect to a filtration $(\calF_m)$, taking values in $Q$ and converging almost surely to $M_\infty$. If $e$ is an $\calF_0$-measurable binary vector, then \begin{align} \E\sum_{m=0}^\infty \|\Phi(M_{m+1})-\Phi(M_m)\|_{1,w}^2 &\leq108\bigl(\E\|M_\infty-e\|_H^4 -\E\|M_0-e\|_H^4\bigr)\notag\\ &\leq108\E\|M_\infty-e\|_H^4. \label{eq:martingale-energy} \end{align}

**Lean.** `Papers.OaiMetricMarkovCotype.martingale_cubic_energy_bound` — `lean/Papers/OaiMetricMarkovCotype/TMartingale.lean:198`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $(M_m)_{m\geq0}$ be an $H$-valued martingale with respect to a filtration $(\calF_m)$, taking values in $Q$ and converging almost surely to $M_\infty$. | `𝓕 : Filtration ℕ mΩ`<br>`M : ℕ → Ω → 𝓑 → ℝ`<br>`Minf e : Ω → 𝓑 → ℝ`<br>`h_process : CubeMartingale μ 𝓕 M Minf` |
| If $e$ is an $\calF_0$-measurable binary vector, | `Minf e : Ω → 𝓑 → ℝ`<br>`h_center : InitialBinaryCenter 𝓕 e` |
| then \begin{align} \E\sum_{m=0}^\infty \\|\Phi(M_{m+1})-\Phi(M_m)\\|_{1,w}^2 &\leq108\bigl(\E\\|M_\infty-e\\|_H^4 -\E\\|M_0-e\\|_H^4\bigr)\notag\\ &\leq108\E\\|M_\infty-e\\|_H^4. \end{align} | then `(∫⁻ ω, ∑' m : ℕ, ENNReal.ofReal (weightedL1Norm w (cubicMap (M (m + 1) ω) - cubicMap (M m ω)) ^ 2) ∂μ) ≤ ENNReal.ofReal (108 * ((∫ ω, quarticPotential w (e ω) (Minf ω) ∂μ) - ∫ ω, quarticPotential w (e ω) (M 0 ω) ∂μ))`<br>then `108 * ((∫ ω, quarticPotential w (e ω) (Minf ω) ∂μ) - ∫ ω, quarticPotential w (e ω) (M 0 ω) ∂μ) ≤ 108 * ∫ ω, quarticPotential w (e ω) (Minf ω) ∂μ` |

Lean also declares what the paper leaves implicit (the objects and their types): `Ω 𝓑 : Type*`, `mΩ : MeasurableSpace Ω`, `Fintype 𝓑`, `μ : Measure Ω`, `IsProbabilityMeasure μ`, `w : 𝓑 → ℝ`.

Lean assumes conditions that the paper's text does not state: `h_finite : FiniteCutIndex 𝓑`, `h_weights : PositiveWeights w`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For \[ \|u\|_{1,w}=\sum_{B\in\mathcal B}w_B|u_B|, \qquad \|u\|_H^2=\sum_{B\in\mathcal B}w_Bu_B^2, \] → `weightedL1Norm` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:171`)
- definition of the paper: The space $H$ is $\R^{\mathcal B}$ with the indicated Hilbert norm. → `weightedHNorm` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:185`)
- definition of the paper: Write $Q=[0,1]^{\mathcal B}$ and let $\langle\cdot,\cdot\rangle_H$ be the weighted Hilbert inner product. → `weightedInner` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:192`)
- definition of the paper: Define \[ \phi(r)=3r^2-2r^3\quad(0\leq r\leq1), \qquad \Phi(u)_B=\phi(u_B)\quad(u\in Q). \] → `cubicMap` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:256`)
- condition of the paper: Fix a finite nonempty set $\mathcal B$ → `FiniteCutIndex` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:154`)
- condition of the paper: positive weights $w_B$ → `PositiveWeights` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:162`)
- condition of the paper: \label{cor:martingale} Let $(M_m)_{m\geq0}$ be an $H$-valued martingale with respect to a filtration $(\calF_m)$, taking values in $Q$ and converging almost surely to $M_\infty$. → `CubeMartingale` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:345`)
- condition of the paper: If $e$ is an $\calF_0$-measurable binary vector, → `InitialBinaryCenter` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:359`)

## Lemma 4.1

**Statement.** \label{lem:comparison} Let $(X_s)_{s\geq0}$ be a stationary Markov chain on $[n]$, and let $x_1,\ldots,x_n$ lie in a metric space $(X,d)$. For $t\in\N$, set $p=1/(t+1)$ and $q=1-p$. If $S$ is independent of the walk and $\Prob(S=s)=pq^s$ for $s\geq0$, then \begin{equation}\label{eq:comparison} \E d(x_{X_S},x_{X_0})^2 \leq\frac{28}{t}\sum_{s=1}^t \E d(x_{X_s},x_{X_0})^2. \end{equation}

**Lean.** `Papers.OaiMetricMarkovCotype.geometric_endpoint_comparison` — `lean/Papers/OaiMetricMarkovCotype/Helpers/Comparison.lean:518`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $(X_s)_{s\geq0}$ be a stationary Markov chain on $[n]$, | `n : ℕ`<br>`U : ℕ → Ω → Fin n`<br>`h_chain : StationaryFiniteChain μ U` |
| and let $x_1,\ldots,x_n$ lie in a metric space $(X,d)$. | `Ω X : Type*`<br>`x : Fin n → X` |
| For $t\in\N$, set $p=1/(t+1)$ | `t : ℕ`<br>`h_time : PositiveTime t` |
| and $q=1-p$. | — (no Lean counterpart recorded) |
| If $S$ is independent of the walk and $\Prob(S=s)=pq^s$ for $s\geq0$, | `S : Ω → ℕ`<br>`h_independent : GeometricIndependentOfWalk μ U S`<br>`h_geometric : GeometricLaw μ S t h_time` |
| then \begin{equation} \E d(x_{X_S},x_{X_0})^2 \leq\frac{28}{t}\sum_{s=1}^t \E d(x_{X_s},x_{X_0})^2. \end{equation} | then `(∫ ω, dist (x (U (S ω) ω)) (x (U 0 ω)) ^ 2 ∂μ) ≤ (28 / (t : ℝ)) * ∑ s ∈ Finset.Icc 1 t, endpointCost μ U x s` |

Lean also declares what the paper leaves implicit (the objects and their types): `MeasurableSpace Ω`, `MetricSpace X`, `μ : Measure Ω`, `IsProbabilityMeasure μ`.

Lean assumes conditions that the paper's text does not state: `h_data : ComparisonData n x`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: Write $\N=\{1,2,\ldots\}$ and $[n]=\{1,\ldots,n\}$. → `StateSet` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:52`)
- definition of the paper: For $t\in\N$, set $p=1/(t+1)$ and $q=1-p$. → `geomKillProb` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:300`)
- condition of the paper: Let $(X_s)_{s\geq0}$ be a stationary Markov chain on $[n]$, → `StationaryFiniteChain` (`lean/Papers/OaiMetricMarkovCotype/Helpers/Comparison.lean:26`)
- condition of the paper: and let $x_1,\ldots,x_n$ lie in a metric space $(X,d)$. → `ComparisonData` (`lean/Papers/OaiMetricMarkovCotype/Helpers/Comparison.lean:36`)
- condition of the paper: For $t\in\N$, → `PositiveTime` (`lean/Papers/OaiMetricMarkovCotype/Helpers/Comparison.lean:41`)
- condition of the paper: If $S$ is independent of the walk → `GeometricIndependentOfWalk` (`lean/Papers/OaiMetricMarkovCotype/Helpers/Comparison.lean:47`)
- condition of the paper: $\Prob(S=s)=pq^s$ for $s\geq0$ → `GeometricLaw` (`lean/Papers/OaiMetricMarkovCotype/Helpers/Comparison.lean:56`)

## Corollary 6.1

**Statement.** \label{cor:complex} For complex scalars, $N_2(\ell_1(\mathbb C))\leq12\sqrt{42}$.

**Lean.** `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_complexEllOne_le` — `lean/Papers/OaiMetricMarkovCotype/TComplex.lean:275`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For complex scalars, $N_2(\ell_1(\mathbb C))\leq12\sqrt{42}$. | then `metricMarkovCotypeConstant ComplexEllOne ≤ ENNReal.ofReal (12 * Real.sqrt 42)` |

**Conditions and readings, and the Lean definitions that carry them.**

- reading: In the cost identities, $B=\sum_i\pi_i\|z_i-\Phi(h_i)\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. → `ApproxCostReading` (`lean/Papers/OaiMetricMarkovCotype/Helpers/StoppedWalk.lean:198`)
- definition of the paper: \label{def:cotype} A metric space $(X,d)$ has metric Markov cotype two with constant $C>0$ if, for every $n,t\in\N$, every probability vector $\pi$, every stochastic matrix $A$ reversible with respect to $\pi$, and every $x_1,\ldots,x_n\in X$, there exist $y_1,\ldots,y_n\in X$ such that \begin{equation}\label{eq:cotype} \sum_i\pi_i d(x_i,y_i)^2 +t\sum_{i,j}\pi_i a_{ij}d(y_i,y_j)^2 \leq C^2\sum_{i,j}\pi_i \left(\frac1t\sum_{s=1}^t A^s\right)_{ij}d(x_i,x_j)^2. \end{equation} → `HasMetricMarkovCotypeTwo` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:137`)
- definition of the paper: The infimum of all such constants is denoted $N_2(X)$. → `metricMarkovCotypeConstant` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:145`)

## Corollary 6.2

**Statement.** \label{cor:extension} There is a universal constant $K<\infty$ such that, for every real Hilbert space $\mathcal H$, every subset $S\subseteq\mathcal H$, and every Lipschitz map $f:S\to\ell_1$, there is an extension $F:\mathcal H\to\ell_1$ with $\Lip(F)\leq K\Lip(f)$.

**Lean.** `Papers.OaiMetricMarkovCotype.lipschitz_extension_hilbert_to_ellOne` — `lean/Papers/OaiMetricMarkovCotype/TExtension.lean:69`

**Status.** proved in Lean, given 1 cited result(s), under 2 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There is a universal constant $K<\infty$ such that, for every real Hilbert space $\mathcal H$, every subset $S\subseteq\mathcal H$, | then `∃ K : ℝ,`<br>`𝓗 : Type u`<br>`HilbertSource 𝓗`<br>`S : Set 𝓗`<br>`ExtensionDomain S` |
| and every Lipschitz map $f:S\to\ell_1$, there is an extension $F:\mathcal H\to\ell_1$ with $\Lip(F)\leq K\Lip(f)$. | `∀ f : S → RealEllOne`<br>`LipschitzIntoEllOne f`<br>then `∃ F : 𝓗 → RealEllOne,`<br>`∀ x : S`<br>then `F x = f x`<br>then `lipConst F ≤ ENNReal.ofReal K * lipConst f` |

Lean also declares what the paper leaves implicit (the objects and their types): `NormedAddCommGroup 𝓗`, `InnerProductSpace ℝ 𝓗`.

Lean assumes conditions that the paper's text does not state: `h_of_gate : MendelNaorExtension.{u}`.

Lean concludes what the paper's text does not state: `0 ≤ K`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: In the cost identities, $B=\sum_i\pi_i\|z_i-\Phi(h_i)\|_{1,w}^2$; occurrences of $B\in\mathcal B$ in coordinate positions denote cut indices. → `ApproxCostReading` (`lean/Papers/OaiMetricMarkovCotype/Helpers/StoppedWalk.lean:198`)
- reading: $\Lip(f)=\inf\{L\geq0:d(f(x),f(y))\leq Ld(x,y)\text{ for all }x,y\text{ in the domain of }f\}$, with $\inf\varnothing=\infty$. → `LipConstReading` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:377`)
- definition of the paper: For a map $f$ between metric spaces, $\Lip(f)$ denotes the least $L\geq0$ such that $d(f(x),f(y))\leq Ld(x,y)$ for all $x,y$ in its domain. → `lipConst` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:369`)
- definition of the paper: For the extension consequence, recall that a metric space $(Z,d_Z)$ has \emph{Markov type two} with constant $M>0$ if \[ \sum_{i,j}\pi_i(A^t)_{ij}d_Z(u_i,u_j)^2 \leq M^2t\sum_{i,j}\pi_i a_{ij}d_Z(u_i,u_j)^2 \] for every $n,t\in\N$, every stochastic matrix $A$ reversible with respect to a probability vector $\pi$, and every $u_1,\ldots,u_n\in Z$. → `HasMarkovTypeTwo` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:429`)
- definition of the paper: \label{def:cotype} A metric space $(X,d)$ has metric Markov cotype two with constant $C>0$ if, for every $n,t\in\N$, every probability vector $\pi$, every stochastic matrix $A$ reversible with respect to $\pi$, and every $x_1,\ldots,x_n\in X$, there exist $y_1,\ldots,y_n\in X$ such that \begin{equation}\label{eq:cotype} \sum_i\pi_i d(x_i,y_i)^2 +t\sum_{i,j}\pi_i a_{ij}d(y_i,y_j)^2 \leq C^2\sum_{i,j}\pi_i \left(\frac1t\sum_{s=1}^t A^s\right)_{ij}d(x_i,x_j)^2. \end{equation} → `HasMetricMarkovCotypeTwo` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:137`)
- definition of the paper: The infimum of all such constants is denoted $N_2(X)$. → `metricMarkovCotypeConstant` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:145`)
- condition of the paper: for every real Hilbert space $\mathcal H$ → `HilbertSource` (`lean/Papers/OaiMetricMarkovCotype/TExtension.lean:25`)
- condition of the paper: every subset $S\subseteq\mathcal H$ → `ExtensionDomain` (`lean/Papers/OaiMetricMarkovCotype/TExtension.lean:32`)
- condition of the paper: every Lipschitz map $f:S\to\ell_1$ → `LipschitzIntoEllOne` (`lean/Papers/OaiMetricMarkovCotype/TExtension.lean:40`)

**Taken from the literature: MendelNaor13, Corollary 1.13.**

What Lean assumes for it: `Papers.OaiMetricMarkovCotype.MendelNaorExtension` (`lean/Papers/OaiMetricMarkovCotype/Basic.lean:453`)

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

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.2 | `thm:main` | `thm:main` | `main.tex:88-93` | `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_realEllOne_le` |
| Lemma 2.1 | `lem:cuts` | `lem:cuts` | `main.tex:200-222` | `Papers.OaiMetricMarkovCotype.cut_decomposition` |
| Lemma 3.1 | `lem:flat` | `lem:flat` | `main.tex:290-298` | `Papers.OaiMetricMarkovCotype.flat_cubic_bound` |
| Corollary 3.2 | `thm:martingale` | `cor:martingale` | `main.tex:345-358` | `Papers.OaiMetricMarkovCotype.martingale_cubic_energy_bound` |
| Lemma 4.1 | `lem:comparison` | `lem:comparison` | `main.tex:385-396` | `Papers.OaiMetricMarkovCotype.geometric_endpoint_comparison` |
| Corollary 6.1 | `thm:complex` | `cor:complex` | `main.tex:596-599` | `Papers.OaiMetricMarkovCotype.metricMarkovCotypeConstant_complexEllOne_le` |
| Corollary 6.2 | `thm:extension` | `cor:extension` | `main.tex:627-633` | `Papers.OaiMetricMarkovCotype.lipschitz_extension_hilbert_to_ellOne` |

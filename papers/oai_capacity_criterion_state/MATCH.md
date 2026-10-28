# The corrected paper and its Lean formalization — oai_capacity_criterion_state

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} Let $T$ be an infinite rooted tree with at most $B<\infty$ children per vertex, and let $0<\lambda<1$. For the broadcast model \eqref{eq:channel}, \[ a_\infty(T,\lambda)>0 \quad\Longleftrightarrow\quad \Capacity_{3,\lambda}(T)>0. \]

**Lean.** `OaiCapacityCriterionState.reconstructs_iff_capacity_pos` — `lean/Papers/OaiCapacityCriterionState/TMain.lean:26`

**Status.** proved in Lean, given 1 cited result(s), under 2 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $T$ be an infinite rooted tree with at most $B<\infty$ children per vertex, | `B : ℕ`<br>`T : BoundedTree B`<br>`hT : MainTree T` |
| and let $0<\lambda<1$. | `lam : ℝ`<br>`hlam : MainLambda lam` |
| For the broadcast model \eqref{eq:channel}, | — (no Lean counterpart recorded) |
| \[ a_\infty(T,\lambda)>0 \quad\Longleftrightarrow\quad | then `0 < limitInfo T lam ↔ 0 < capacity3 T lam` |
| \Capacity_{3,\lambda}(T)>0. \] | then `0 < limitInfo T lam ↔ 0 < capacity3 T lam` |

Lean assumes conditions that the paper's text does not state: `hCompanion_of_gate : CompanionMomentSaving`, `hpin1 : EuclideanNormPin`, `hpin2 : ProductRulePin`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: For $x\in\mathbb R^3$, $|x|^2=x_1^2+x_2^2+x_3^2$. → `EuclideanNormPin` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:212`)
- reading: The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. → `ProductRulePin` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:678`)
- condition of the paper: Let $T$ be an infinite rooted tree with at most $B<\infty$ children per vertex, → `MainTree` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:120`)
- condition of the paper: and let $0<\lambda<1$. → `MainLambda` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:128`)
- definition of the paper: Write $|v|$ for the depth of a vertex, $\children(v)$ for its children, and $L_n=\{v:|v|=n\}$. → `level` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:51`)
- definition of the paper: Give the root a uniform spin in $[4]$, and transmit spins independently along edges conditional on their parent spins, using \begin{equation}\label{eq:channel} P_\lambda(j\mid i) =\lambda\mathbf1_{\{i=j\}}+\frac{1-\lambda}{4}. \end{equation} → `broadcastJoint` (`lean/Papers/OaiCapacityCriterionState/Helpers/Broadcast.lean:42`)
- definition of the paper: For the uniform probability vector $\unif=(1/4,1/4,1/4,1/4)$, put \[ a_n(T,\lambda)= \E\,\TV\bigl(\Prob(\sigma_\rho\in\cdot\mid\sigma_{L_n}), \unif\bigr), \qquad \TV(p,\unif)=\frac12\sum_{i=1}^4|p_i-1/4|. \] → `levelInfo` (`lean/Papers/OaiCapacityCriterionState/Helpers/Broadcast.lean:348`)
- definition of the paper: We say that \emph{reconstruction occurs} if its limit $a_\infty(T,\lambda)$ is positive. → `limitInfo` (`lean/Papers/OaiCapacityCriterionState/Helpers/Broadcast.lean:569`)
- definition of the paper: A nonnegative flow $\theta$ to infinity assigns a nonnegative number to each edge, with incoming flow equal to the sum of outgoing flows at every nonroot vertex. Its mass is \[ |\theta|=\sum_{w\in\children(\rho)}\theta(\rho,w). \] → `IsFlow` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:167`)
- definition of the paper: For an edge $e$, let $|e|$ be the depth of its child endpoint, and let $\partial T$ denote the infinite rays from the root. → `BoundedTree.rays` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:192`)
- definition of the paper: \begin{align} V_\lambda(\theta,\xi) &=\sum_{e\in\xi}\bigl(\lambda^{-2|e|}\theta(e)\bigr)^2, \qquad \xi\in\partial T,\label{eq:potential}\\ \Capacity_{3,\lambda}(T) &=\sup\left\{|\theta|: \sup_{\xi\in\partial T}V_\lambda(\theta,\xi)\leq1\right\}. \label{eq:capacity} \end{align} → `capacity3` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:266`)
- definition of the paper: Throughout, set \[ r=\lambda^2\in(0,1). \] → `sqParam` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:134`)
- definition of the paper: An experiment consists of an observation about a uniform input spin in $[4]$. Let $p$ be its posterior vector and $\mu$ the law of $p$ under the marginal law of the observation. → `PosteriorLaw` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:47`)
- definition of the paper: Define \[ L=\begin{pmatrix} 1&1&-1&-1\\ 1&-1&1&-1\\ 1&-1&-1&1 \end{pmatrix},\qquad x=Lp,\qquad A(p)=|x|^2, \] → `quadStat` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:176`)
- definition of the paper: \begin{equation}\label{eq:statistics} m(\mu)=\E_\mu A, \qquad \tau(\mu)=\E_\mu[x_1x_2x_3], \qquad h(\mu)=|\tau(\mu)|. \end{equation} → `quadInfo` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:219`)
- definition of the paper: In a channel step with parameter $t\in[0,1]$, first transmit a uniform input $I$ to $J$ through $P_t$, then observe an experiment about $J$. The uniform distribution is stationary and the channel is symmetric, so the posterior about $I$ is $\unif+t(p-\unif)$. → `channelStep` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:262`)
- definition of the paper: \begin{equation}\label{eq:channel-scaling} x\longmapsto tx,\qquad m\longmapsto t^2m, \qquad \tau\longmapsto t^3\tau, \qquad h\longmapsto t^3h. \end{equation} → `channelScaledMoments` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:322`)
- definition of the paper: The completely revealing experiment has $m=3$, while the uninformative experiment has $m=h=0$. → `extremeExperiments` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:395`)
- definition of the paper: If two observations are independent conditional on the same input spin, write $\mu\star\nu$ for their combined posterior law. The normalized-product rule below is standard in posterior recursions for reconstruction; see M\'ezard and Montanari \cite[Sections~2.2--2.4]{MM06}. Sample $p,q$ independently from their marginal posterior laws $\mu,\nu$. The joint marginal law of the observations is obtained by weighting this product law by \begin{equation}\label{eq:product-rule} Z=4\sum_{i=1}^4p_iq_i, \qquad P_i=\frac{4p_iq_i}{Z}. \end{equation} → `starLaw` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:516`)

**Taken from the literature: OpenAI26Potts, Proposition 3.2 and Equations (3.8)--(3.9).**

What Lean assumes for it: `OaiCapacityCriterionState.CompanionMomentSaving` (`lean/Papers/OaiCapacityCriterionState/Helpers/CitedGates.lean:32`)

```lean
def CompanionMomentSaving : Sort 0 :=
  ∃ C : Set (Measure (Fin 4 → ℝ)), -- @realizes \calC(class of symmetric posterior laws)
    (∀ mu ∈ C, IsPosteriorLaw mu ∧ IsSymmetricLaw mu) ∧
    revealingLaw ∈ C ∧ uninformativeLaw ∈ C ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C) ∧
    (∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C) ∧
    ∀ mu ∈ C, ∀ nu ∈ C,
      quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu -
        (1 / 1000 : ℝ) * -- @realizes c(the fixed positive constant 1/1000)
          ((∫ p, quadStat p ^ 2 ∂mu) * quadInfo nu +
            quadInfo mu * ∫ p, quadStat p ^ 2 ∂nu)
```

## Proposition 2.1

**Statement.** \label{prop:companion} There is a class $\calC$ of symmetric posterior laws containing the revealing and uninformative laws and preserved by channel steps with any parameter in $[0,1]$ and by conditionally independent products. For $\mu,\nu\in\calC$, \begin{equation}\label{eq:moment-saving} m(\mu\star\nu)\leq m(\mu)+m(\nu) -c\left(\E_\mu[A^2]m(\nu)+m(\mu)\E_\nu[A^2]\right), \qquad c=\frac1{1000}. \end{equation}

**Lean.** no declaration

**Status.** taken from the literature as cited; not proved here.

**Taken from the literature: OpenAI26Potts, Proposition 3.2 and Equations (3.8)--(3.9).**

What Lean assumes for it: `OaiCapacityCriterionState.CompanionMomentSaving` (`lean/Papers/OaiCapacityCriterionState/Helpers/CitedGates.lean:32`)

```lean
def CompanionMomentSaving : Sort 0 :=
  ∃ C : Set (Measure (Fin 4 → ℝ)), -- @realizes \calC(class of symmetric posterior laws)
    (∀ mu ∈ C, IsPosteriorLaw mu ∧ IsSymmetricLaw mu) ∧
    revealingLaw ∈ C ∧ uninformativeLaw ∈ C ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ mu ∈ C, channelStep t mu ∈ C) ∧
    (∀ mu ∈ C, ∀ nu ∈ C, starLaw mu nu ∈ C) ∧
    ∀ mu ∈ C, ∀ nu ∈ C,
      quadInfo (starLaw mu nu) ≤ quadInfo mu + quadInfo nu -
        (1 / 1000 : ℝ) * -- @realizes c(the fixed positive constant 1/1000)
          ((∫ p, quadStat p ^ 2 ∂mu) * quadInfo nu +
            quadInfo mu * ∫ p, quadStat p ^ 2 ∂nu)
```

## Lemma 3.1

**Statement.** \label{lem:flow} Suppose nonnegative finite labels $(z_v)_{v\in T}$ satisfy \begin{equation}\label{eq:label-recursion} z_v\leq\sum_{w\in\children(v)} \frac{r z_w}{\sqrt{1+z_w^2}}. \end{equation} Then there is a flow of mass $z_\rho$ whose potential \eqref{eq:potential} is at most one on every ray. In particular, $\Capacity_{3,\lambda}(T)\geq z_\rho$.

**Lean.** `OaiCapacityCriterionState.exists_flow_of_labels` — `lean/Papers/OaiCapacityCriterionState/Helpers/Flow.lean:199`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Suppose nonnegative finite labels $(z_v)_{v\in T}$ satisfy | `z : List (Fin B) → ℝ`<br>`hz : FlowLabelRecursion T lam z` |
| \begin{equation} z_v\leq\sum_{w\in\children(v)} \frac{r z_w}{\sqrt{1+z_w^2}}. \end{equation} | `hz : FlowLabelRecursion T lam z` |
| Then there is a flow of mass $z_\rho$ whose potential \eqref{eq:potential} is at most one on every ray. | then `∃ theta : List (Fin B) → ℝ,`<br>then `IsFlow T theta`<br>then `flowMass T theta = z []`<br>`∀ xi ∈ T.rays`<br>then `pathPotential lam theta xi ≤ 1` |
| In particular, $\Capacity_{3,\lambda}(T)\geq z_\rho$. | then `ENNReal.ofReal (z []) ≤ capacity3 T lam` |

Lean also declares what the paper leaves implicit (the objects and their types): `B : ℕ`, `T : BoundedTree B`, `lam : ℝ`.

Lean assumes conditions that the paper's text does not state: `hT : MainTree T`, `hlam : MainLambda lam`.

**Conditions and readings, and the Lean definitions that carry them.**

- condition of the paper: \label{lem:flow} Suppose nonnegative finite labels $(z_v)_{v\in T}$ satisfy \begin{equation}\label{eq:label-recursion} z_v\leq\sum_{w\in\children(v)} \frac{r z_w}{\sqrt{1+z_w^2}}. \end{equation} → `FlowLabelRecursion` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:154`)
- definition of the paper: Write $|v|$ for the depth of a vertex, $\children(v)$ for its children, and $L_n=\{v:|v|=n\}$. → `level` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:51`)
- definition of the paper: Throughout, set \[ r=\lambda^2\in(0,1). \] → `sqParam` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:134`)
- definition of the paper: A nonnegative flow $\theta$ to infinity assigns a nonnegative number to each edge, with incoming flow equal to the sum of outgoing flows at every nonroot vertex. Its mass is \[ |\theta|=\sum_{w\in\children(\rho)}\theta(\rho,w). \] → `IsFlow` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:167`)
- definition of the paper: For an edge $e$, let $|e|$ be the depth of its child endpoint, and let $\partial T$ denote the infinite rays from the root. → `BoundedTree.rays` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:192`)
- definition of the paper: \begin{align} V_\lambda(\theta,\xi) &=\sum_{e\in\xi}\bigl(\lambda^{-2|e|}\theta(e)\bigr)^2, \qquad \xi\in\partial T,\label{eq:potential}\\ \Capacity_{3,\lambda}(T) &=\sup\left\{|\theta|: \sup_{\xi\in\partial T}V_\lambda(\theta,\xi)\leq1\right\}. \label{eq:capacity} \end{align} → `capacity3` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:266`)
- condition of the paper: Let $T$ be an infinite rooted tree with at most $B<\infty$ children per vertex, → `MainTree` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:120`)
- condition of the paper: and let $0<\lambda<1$. → `MainLambda` (`lean/Papers/OaiCapacityCriterionState/Helpers/Trees.lean:128`)

## Lemma 4.1

**Statement.** \label{lem:local-moments} Fix $0<\lambda<1$. Let $\mu,\nu$ be symmetric posterior laws, with $\nu$ obtained by a channel step of parameter $\lambda$. There is a finite constant $C=C(\lambda)$ such that \begin{align} m(\mu\star\nu) &\geq m(\mu)+m(\nu) -C\bigl(h(\mu)m(\nu)+m(\mu)h(\nu)\bigr), \label{eq:local-m-lower}\\ h(\mu\star\nu) &\leq h(\mu)+h(\nu)+C m(\mu)m(\nu). \label{eq:local-h-upper} \end{align} The first inequality holds with $C=7$.

**Lean.** `OaiCapacityCriterionState.local_moment_bounds` — `lean/Papers/OaiCapacityCriterionState/Helpers/LocalMoments.lean:607`

**Status.** proved in Lean, under 2 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Fix $0<\lambda<1$. | `lam : ℝ`<br>`hlam : LocalMomentsLambda lam` |
| Let $\mu,\nu$ be symmetric posterior laws, | `∀ mu nu : PosteriorLaw`<br>`LocalMomentsSymmetry mu nu` |
| with $\nu$ obtained by a channel step of parameter $\lambda$. | `LocalMomentsChannel lam nu` |
| There is a finite constant $C=C(\lambda)$ such that | then `∃ C : ℝ,` |
| \begin{align} m(\mu\star\nu) &\geq m(\mu)+m(\nu) -C\bigl(h(\mu)m(\nu)+m(\mu)h(\nu)\bigr), \\ | then `quadInfo (starLaw mu nu) ≥ quadInfo mu + quadInfo nu - C * (absThird mu * quadInfo nu + quadInfo mu * absThird nu)` |
| h(\mu\star\nu) &\leq h(\mu)+h(\nu)+C m(\mu)m(\nu). \end{align} | then `absThird (starLaw mu nu) ≤ absThird mu + absThird nu + C * quadInfo mu * quadInfo nu` |
| The first inequality holds with $C=7$. | then `quadInfo (starLaw mu nu) ≥ quadInfo mu + quadInfo nu - 7 * (absThird mu * quadInfo nu + quadInfo mu * absThird nu)` |

Lean assumes conditions that the paper's text does not state: `hpin1 : EuclideanNormPin`, `hpin2 : ProductRulePin`.

Lean concludes what the paper's text does not state: `0 < C`.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: For $x\in\mathbb R^3$, $|x|^2=x_1^2+x_2^2+x_3^2$. → `EuclideanNormPin` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:212`)
- reading: The combined posterior law is the law of $P$ under $Z\,d(\mu\otimes\nu)$, with $P_i=4p_iq_i/Z$ on $\{Z>0\}$ and any measurable simplex-valued extension on $\{Z=0\}$. → `ProductRulePin` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:678`)
- condition of the paper: \label{lem:local-moments} Fix $0<\lambda<1$. → `LocalMomentsLambda` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:692`)
- condition of the paper: Let $\mu,\nu$ be symmetric posterior laws, → `LocalMomentsSymmetry` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:699`)
- condition of the paper: with $\nu$ obtained by a channel step of parameter $\lambda$. → `LocalMomentsChannel` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:707`)
- definition of the paper: An experiment consists of an observation about a uniform input spin in $[4]$. Let $p$ be its posterior vector and $\mu$ the law of $p$ under the marginal law of the observation. → `PosteriorLaw` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:47`)
- definition of the paper: Define \[ L=\begin{pmatrix} 1&1&-1&-1\\ 1&-1&1&-1\\ 1&-1&-1&1 \end{pmatrix},\qquad x=Lp,\qquad A(p)=|x|^2, \] → `quadStat` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:176`)
- definition of the paper: \begin{equation}\label{eq:statistics} m(\mu)=\E_\mu A, \qquad \tau(\mu)=\E_\mu[x_1x_2x_3], \qquad h(\mu)=|\tau(\mu)|. \end{equation} → `quadInfo` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:219`)
- definition of the paper: In a channel step with parameter $t\in[0,1]$, first transmit a uniform input $I$ to $J$ through $P_t$, then observe an experiment about $J$. The uniform distribution is stationary and the channel is symmetric, so the posterior about $I$ is $\unif+t(p-\unif)$. → `channelStep` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:262`)
- definition of the paper: If two observations are independent conditional on the same input spin, write $\mu\star\nu$ for their combined posterior law. The normalized-product rule below is standard in posterior recursions for reconstruction; see M\'ezard and Montanari \cite[Sections~2.2--2.4]{MM06}. Sample $p,q$ independently from their marginal posterior laws $\mu,\nu$. The joint marginal law of the observations is obtained by weighting this product law by \begin{equation}\label{eq:product-rule} Z=4\sum_{i=1}^4p_iq_i, \qquad P_i=\frac{4p_iq_i}{Z}. \end{equation} → `starLaw` (`lean/Papers/OaiCapacityCriterionState/Helpers/PosteriorLaws.lean:516`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `main.tex:95-104` | `OaiCapacityCriterionState.reconstructs_iff_capacity_pos` |
| Proposition 2.1 | `prop:companion` | `prop:companion` | `main.tex:290-301` | — |
| Lemma 3.1 | `lem:flow` | `lem:flow` | `main.tex:323-332` | `OaiCapacityCriterionState.exists_flow_of_labels` |
| Lemma 4.1 | `lem:local-moments` | `lem:local-moments` | `main.tex:435-449` | `OaiCapacityCriterionState.local_moment_bounds` |

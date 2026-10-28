# The corrected paper and its Lean formalization — oai_exact_semidefinite_lift

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} There exist fixed matrices $A_1,\ldots,A_{23},B_1,\ldots,B_{307} \in\Sym^{100}$ such that, for every $x=(X,Z,y)\in\mathcal V$, \[ x\in K\quad\Longleftrightarrow\quad \text{there exists }v\in\R^{307}\text{ with } \sum_{\nu=1}^{23}x_\nu A_\nu+ \sum_{j=1}^{307}v_jB_j\succeq0. \] The equivalence holds on the entire closed cone, including points with singular $X$.

**Lean.** `Papers.OaiExactSemidefiniteLift.exact_semidefinite_lift` — `lean/Papers/OaiExactSemidefiniteLift/TMain.lean:30`

**Status.** proved in Lean, under 2 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There exist fixed matrices $A_1,\ldots,A_{23},B_1,\ldots,B_{307} \in\Sym^{100}$ such that, for every $x=(X,Z,y)\in\mathcal V$, | ≈ then `∃ (A : Fin 23 → Mat 100) (B : Fin 307 → Mat 100),`<br>≈ `∀ ν`<br>≈ then `(A ν).IsSymm`<br>≈ `∀ j`<br>≈ then `(B j).IsSymm`<br>`∀ x : V` |
| \[ x\in K\quad\Longleftrightarrow\quad | then `x ∈ coneK ↔ ∃ v : Fin 307 → ℝ, (∑ ν : Fin 23, outputCoords x ν • A ν + ∑ j : Fin 307, v j • B j).PosSemidef` |
| \text{there exists }v\in\R^{307}\text{ with } \sum_{\nu=1}^{23}x_\nu A_\nu+ \sum_{j=1}^{307}v_jB_j\succeq0. \] | then `x ∈ coneK ↔ ∃ v : Fin 307 → ℝ, (∑ ν : Fin 23, outputCoords x ν • A ν + ∑ j : Fin 307, v j • B j).PosSemidef` |
| The equivalence holds on the entire closed cone, including points with singular $X$. | `∀ x : V` |

A row marked ≈ was given these phrases with many rows of its result at once, not on its own.

**Conditions and readings, and the Lean definitions that carry them.**

- reading: In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$. → `MomentBasisPinned` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/Moment.lean:83`)
- reading: The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. → `ComplexTrigPolyPinned` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:324`)
- definition of the paper: Identify $\mathcal V$ with $\R^{23}$ by listing the upper triangular entries of $X$, then those of $Z$, each in lexicographic order of $(i,j)$, followed by $y_1,y_2,y_3$. → `outputCoords` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:115`)
- definition of the paper: For an output point $(X,Z,y)$, impose \begin{equation}\label{eq:output} \Lambda(\mathcal X)=X,\qquad \Lambda(\mathcal Z)=Z,\qquad \Lambda\bigl(Y_\theta(\eta,\xi)\bigr)=y. \end{equation} → `OutputEquations` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/Moment.lean:51`)
- definition of the paper: Indeed, set $(f_1,\ldots,f_5)= (1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ and define $H(\Lambda)\in\mathbb S^{100}$ by \begin{equation}\label{eq:moment-matrix} H(\Lambda)_{(i,a),(j,b)} =\Lambda\bigl(f_a f_b (L_\theta)_{ij}\bigr), \qquad 1\leq i,j\leq20,\quad 1\leq a,b\leq5. \end{equation} → `momentMatrixH` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/Moment.lean:75`)
- definition of the paper: Let $\mathcal T_j$ be the real vector space of trigonometric polynomials of degree at most $j$, with basis \[ 1,\cos\theta,\sin\theta,\ldots,\cos(j\theta),\sin(j\theta). \] → `IsTrigPolyLE` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:294`)
- definition of the paper: Let $\mathcal E$ be the space of real functions of $(\theta,\mathcal X,\mathcal Z,\eta,\xi)$ that are linear homogeneous in the $22$ coordinates of $(\mathcal X,\mathcal Z,\eta,\xi)\in \mathbb S^4\times\mathbb S^4\times\mathbb R^2$, with coefficients in $\mathcal T_7$. → `LiftSpace` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/FunctionSpace.lean:58`)
- definition of the paper: Our lifting variable is a real linear functional $\Lambda:\mathcal E\to\mathbb R$; on vectors and matrices we apply it entrywise. → `LiftFunctional` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/FunctionSpace.lean:155`)
- definition of the paper: We write $K=K(p,e)$. → `coneK` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:100`)

## Lemma 2.1

**Statement.** \label{lem:gram} For every $\theta,\eta,\xi\in\mathbb R$, \begin{equation}\label{eq:gram} \widetilde F_\theta(\eta,\xi) \widetilde F_\theta(\eta,\xi)^T =Q\bigl(Y_\theta(\eta,\xi)\bigr). \end{equation} In particular, $Q(y)\succeq0$ for every $y\in\mathbb R^3$.

**Lean.** `Papers.OaiExactSemidefiniteLift.gram_identity` — `lean/Papers/OaiExactSemidefiniteLift/Helpers/Gram.lean:132`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every $\theta,\eta,\xi\in\mathbb R$, | `∀ θ η ξ : ℝ` |
| \begin{equation} \widetilde F_\theta(\eta,\xi) \widetilde F_\theta(\eta,\xi)^T =Q\bigl(Y_\theta(\eta,\xi)\bigr). \end{equation} | then `realify (Fθ θ η ξ) * (realify (Fθ θ η ξ))ᵀ = Qmat (Yplane θ η ξ)` |
| In particular, $Q(y)\succeq0$ for every $y\in\mathbb R^3$. | `∀ y : Fin 3 → ℝ`<br>then `(Qmat y).PosSemidef` |

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For $y=(y_1,y_2,y_3)\in\R^3$, define \begin{equation}\label{eq:Q} Q(y)=\begin{pmatrix} y_1^2+y_2^2&-y_1y_2&-y_1y_3\\ -y_1y_2&y_2^2+y_3^2&-y_2y_3\\ -y_1y_3&-y_2y_3&y_3^2+y_1^2 \end{pmatrix}. \end{equation} → `Qmat` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:62`)
- definition of the paper: For $\theta\in\mathbb R$, set \[ c=\cos\theta,\qquad s=\sin\theta,\qquad w=e^{i\theta}, \qquad d(\theta)=(c,s,0),\qquad k=(0,0,1), \] → `dVec` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:122`)
- definition of the paper: and write \[ Y_\theta(\eta,\xi)=\eta d(\theta)+\xi k \qquad (\eta,\xi\in\mathbb R). \] → `Yplane` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:138`)
- definition of the paper: For a complex matrix $F=(f_1,f_2)\in\mathbb C^{3\times2}$, define its realification by \[ \widetilde F=(\operatorname{Re}f_1,\operatorname{Im}f_1, \operatorname{Re}f_2,\operatorname{Im}f_2). \] → `realify` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:145`)
- definition of the paper: \begin{equation}\label{eq:U} U(\theta)=\frac1{\sqrt2} \begin{pmatrix} -w^{-1}&-w\\ sw^{-2}&sw^2\\ cw^{-2}&-cw^2 \end{pmatrix},\qquad V_0=\frac1{\sqrt2} \begin{pmatrix}0&0\\ i&i\\1&1\end{pmatrix}, \qquad F_\theta(\eta,\xi)=\eta U(\theta)+\xi V_0. \end{equation} → `Umat` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:163`)

## Lemma 2.2

**Statement.** \label{lem:slice} For every $\theta,\eta,\xi\in\R$ and $\mathcal X,\mathcal Z\in\Sym^4$, \begin{equation}\label{eq:slice-equivalence} (\mathcal X,\mathcal Z,Y_\theta(\eta,\xi))\in K \quad\Longleftrightarrow\quad L_\theta(\mathcal X,\mathcal Z,\eta,\xi)\succeq0. \end{equation} In particular, $p$ is hyperbolic with respect to $e$. If $\mathcal X\succ0$, the conditions in \eqref{eq:slice-equivalence} are also equivalent to $\mathcal Z\succeq\Phi_{Y_\theta(\eta,\xi)}(\mathcal X^{-1})$.

**Lean.** `Papers.OaiExactSemidefiniteLift.slice_equivalence` — `lean/Papers/OaiExactSemidefiniteLift/Helpers/Slice.lean:432`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For every $\theta,\eta,\xi\in\R$ | `θ η ξ : ℝ`<br>`θ η ξ : ℝ` |
| and $\mathcal X,\mathcal Z\in\Sym^4$, | `𝒳 𝒵 : Sym4`<br>`𝒳 𝒵 : Sym4` |
| \begin{equation} (\mathcal X,\mathcal Z,Y_\theta(\eta,\xi))\in K \quad\Longleftrightarrow\quad | then `(𝒳, 𝒵, Yplane θ η ξ) ∈ coneK ↔ (slicePencil θ 𝒳 𝒵 η ξ).PosSemidef` |
| L_\theta(\mathcal X,\mathcal Z,\eta,\xi)\succeq0. \end{equation} | then `(𝒳, 𝒵, Yplane θ η ξ) ∈ coneK ↔ (slicePencil θ 𝒳 𝒵 η ξ).PosSemidef` |
| In particular, $p$ is hyperbolic with respect to $e$. | then `Toolkit.Foundations.Algebra.IsHyperbolic pPoly eDir` |
| If $\mathcal X\succ0$, the conditions in \eqref{eq:slice-equivalence} are also equivalent to $\mathcal Z\succeq\Phi_{Y_\theta(\eta,\xi)}(\mathcal X^{-1})$. | `SlicePosDef 𝒳`<br>then `(𝒳, 𝒵, Yplane θ η ξ) ∈ coneK ↔ ((𝒵 : Mat 4) - PhiMap (Yplane θ η ξ) (𝒳 : Mat 4)⁻¹).PosSemidef` |

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: We use the closed-cone convention \[ K(p,e)=\{x:\text{every root of }t\mapsto p(te-x) \text{ is nonnegative}\}. \] → `closedCone` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:54`)
- definition of the paper: We write $K=K(p,e)$. → `coneK` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:100`)
- definition of the paper: On the space $\mathcal V=\Sym^4\times\Sym^4\times\R^3$, define \begin{equation}\label{eq:p} p(X,Z,y)=\det\!\left((\det X)Z-\Phi_y(\adj X)\right), \qquad e=(I_4,I_4,0), \end{equation} → `pPoly` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:87`)
- definition of the paper: For $a\in\R$, $r\in\R^3$, and $T\in\Sym^3$, set \begin{equation}\label{eq:Phi} \Phi_y\!\begin{pmatrix}a&r^T\\r&T\end{pmatrix} =\begin{pmatrix} \tr(Q(y)T)&-r^TQ(y)\\ -Q(y)r&aQ(y) \end{pmatrix}. \end{equation} → `PhiMap` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:75`)
- definition of the paper: If $r_1,\ldots,r_4$ are the columns of $\widetilde F_\theta(\eta,\xi)$, direct multiplication and Lemma~\ref{lem:gram} give \begin{equation}\label{eq:Phi-factor} \sum_{j=1}^4 B(r_j)^TWB(r_j) =\Phi_{Y_\theta(\eta,\xi)}(W) \qquad(W\in\Sym^4). \end{equation} → `phiFactorIdentity` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/Slice.lean:76`)
- definition of the paper: For a real column $r\in\R^3$ and a real vector $u=(u_0,u')\in\R\times\R^3$, define \begin{equation}\label{eq:BJ} B(r)=\begin{pmatrix}0&r^T\\-r&0_{3\times3}\end{pmatrix}, \qquad J_u=\begin{pmatrix}u'&-u_0I_3\end{pmatrix}. \end{equation} → `Bskew` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:190`)
- definition of the paper: Write $\mathcal X,\mathcal Z\in\Sym^4$ for the matrix variables on a slice, and define \begin{equation}\label{eq:slice-pencil} L_\theta(\mathcal X,\mathcal Z,\eta,\xi) =\begin{pmatrix} I_4\otimes\mathcal X&\mathcal B_\theta(\eta,\xi)\\ \mathcal B_\theta(\eta,\xi)^T&\mathcal Z \end{pmatrix}, \qquad \mathcal B_\theta(\eta,\xi)= \begin{pmatrix}B(r_1)\\B(r_2)\\B(r_3)\\B(r_4)\end{pmatrix}. \end{equation} → `slicePencil` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:258`)
- definition of the paper: and write \[ Y_\theta(\eta,\xi)=\eta d(\theta)+\xi k \qquad (\eta,\xi\in\mathbb R). \] → `Yplane` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:138`)
- condition of the paper: If $\mathcal X\succ0$, → `SlicePosDef` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:316`)

## Lemma 3.1

**Statement.** \label{lem:matching} Let $S\in\mathbb S^3$ and let $z\in\mathbb R^3$ satisfy $(z_1,z_2)\ne(0,0)$. There is a matrix $C(\theta)\in\mathbb C^{3\times2}$ whose entries are trigonometric polynomials of degree at most two such that, for all $\theta,\eta,\xi\in\mathbb R$, \begin{equation}\label{eq:matching} \begin{aligned} \widetilde C(\theta)\widetilde C(\theta)^T&=Q(z),\\ \langle F_\theta(\eta,\xi),C(\theta)\rangle_S &=\operatorname{tr}\bigl(SQ(Y_\theta(\eta,\xi),z)\bigr). \end{aligned} \end{equation}

**Lean.** `Papers.OaiExactSemidefiniteLift.matching_exists` — `lean/Papers/OaiExactSemidefiniteLift/Helpers/Matching.lean:278`

**Status.** proved in Lean, under 1 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $S\in\mathbb S^3$ and let $z\in\mathbb R^3$ satisfy $(z_1,z_2)\ne(0,0)$. | `S : Sym3`<br>`z : Fin 3 → ℝ`<br>`hz : MatchingNondegenerate z` |
| There is a matrix $C(\theta)\in\mathbb C^{3\times2}$ whose entries are trigonometric polynomials of degree at most two such that, for all $\theta,\eta,\xi\in\mathbb R$, | then `∃ C : ℝ → Matrix (Fin 3) (Fin 2) ℂ,`<br>`∀ i j`<br>then `IsComplexTrigPolyLE 2 (fun θ => C θ i j)`<br>`∀ θ η ξ : ℝ` |
| \begin{equation} \begin{aligned} \widetilde C(\theta)\widetilde C(\theta)^T&=Q(z),\\ \langle F_\theta(\eta,\xi),C(\theta)\rangle_S &=\operatorname{tr}\bigl(SQ(Y_\theta(\eta,\xi),z)\bigr). \end{aligned} \end{equation} | then `realify (C θ) * (realify (C θ))ᵀ = Qmat z`<br>then `weightedPairing S (Fθ θ η ξ) (C θ) = ((S : Mat 3) * Qpol (Yplane θ η ξ) z).trace` |

**Conditions and readings, and the Lean definitions that carry them.**

- reading: The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. → `ComplexTrigPolyPinned` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:324`)
- condition of the paper: \label{lem:matching} Let $S\in\mathbb S^3$ and let $z\in\mathbb R^3$ satisfy $(z_1,z_2)\ne(0,0)$. → `MatchingNondegenerate` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:309`)
- definition of the paper: Write \[ Q(y,z)=\tfrac12\bigl(Q(y+z)-Q(y)-Q(z)\bigr) \] for the symmetric bilinear polarization of $Q$, so that $Q(y,y)=Q(y)$. → `Qpol` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:275`)
- definition of the paper: For $S\in\mathbb S^3$ and $F,H\in\mathbb C^{3\times2}$, put \[ \langle F,H\rangle_S =\operatorname{Re}\operatorname{tr}(F^*SH) =\operatorname{tr}(\widetilde F^T S\widetilde H). \] → `weightedPairing` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:283`)
- definition of the paper: For a complex matrix $F=(f_1,f_2)\in\mathbb C^{3\times2}$, define its realification by \[ \widetilde F=(\operatorname{Re}f_1,\operatorname{Im}f_1, \operatorname{Re}f_2,\operatorname{Im}f_2). \] → `realify` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:145`)
- definition of the paper: \begin{equation}\label{eq:U} U(\theta)=\frac1{\sqrt2} \begin{pmatrix} -w^{-1}&-w\\ sw^{-2}&sw^2\\ cw^{-2}&-cw^2 \end{pmatrix},\qquad V_0=\frac1{\sqrt2} \begin{pmatrix}0&0\\ i&i\\1&1\end{pmatrix}, \qquad F_\theta(\eta,\xi)=\eta U(\theta)+\xi V_0. \end{equation} → `Umat` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:163`)
- definition of the paper: For $\theta\in\mathbb R$, set \[ c=\cos\theta,\qquad s=\sin\theta,\qquad w=e^{i\theta}, \qquad d(\theta)=(c,s,0),\qquad k=(0,0,1), \] → `dVec` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:122`)
- definition of the paper: and write \[ Y_\theta(\eta,\xi)=\eta d(\theta)+\xi k \qquad (\eta,\xi\in\mathbb R). \] → `Yplane` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:138`)
- definition of the paper: A complex trigonometric polynomial of degree at most $j$ is a linear combination of $e^{i\ell\theta}$ for $-j\leq\ell\leq j$. → `IsComplexTrigPolyLE` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:302`)

## Proposition 4.1

**Statement.** \label{prop:lift} For $(X,Z,y)\in\mathbb S^4\times\mathbb S^4\times\mathbb R^3$, the following are equivalent: \begin{enumerate} \item $(X,Z,y)\in K$; \item there is a real linear functional $\Lambda:\mathcal E\to\mathbb R$ satisfying~\eqref{eq:output} and $H(\Lambda)\succeq0$. \end{enumerate}

**Lean.** `Papers.OaiExactSemidefiniteLift.lift_equivalence` — `lean/Papers/OaiExactSemidefiniteLift/Helpers/Lift.lean:22`

**Status.** proved in Lean, under 2 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| For $(X,Z,y)\in\mathbb S^4\times\mathbb S^4\times\mathbb R^3$, the following are equivalent: | `X Z : Sym4`<br>`y : Fin 3 → ℝ`<br>then `(X, Z, y) ∈ coneK ↔ ∃ Λ : LiftFunctional, OutputEquations Λ X Z y ∧ (momentMatrixH Λ).PosSemidef` |
| \begin{enumerate} \item $(X,Z,y)\in K$; | then `(X, Z, y) ∈ coneK ↔ ∃ Λ : LiftFunctional, OutputEquations Λ X Z y ∧ (momentMatrixH Λ).PosSemidef` |
| \item there is a real linear functional $\Lambda:\mathcal E\to\mathbb R$ satisfying~\eqref{eq:output} and $H(\Lambda)\succeq0$. \end{enumerate} | then `(X, Z, y) ∈ coneK ↔ ∃ Λ : LiftFunctional, OutputEquations Λ X Z y ∧ (momentMatrixH Λ).PosSemidef` |

**Conditions and readings, and the Lean definitions that carry them.**

- reading: In the moment-matrix definition, $(f_1,\ldots,f_5)=(1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ are real functions and $H(\Lambda)\in\mathbb S^{100}$ is indexed by $(i,a)$ with $1\leq i\leq20$ and $1\leq a\leq5$. → `MomentBasisPinned` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/Moment.lean:83`)
- reading: The linear combination is finite, with coefficients in $\mathbb C$ independent of $\theta$ and indices $\ell\in\mathbb Z$ satisfying $-j\leq\ell\leq j$. → `ComplexTrigPolyPinned` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:324`)
- definition of the paper: We write $K=K(p,e)$. → `coneK` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:100`)
- definition of the paper: and write \[ Y_\theta(\eta,\xi)=\eta d(\theta)+\xi k \qquad (\eta,\xi\in\mathbb R). \] → `Yplane` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:138`)
- definition of the paper: Let $\mathcal E$ be the space of real functions of $(\theta,\mathcal X,\mathcal Z,\eta,\xi)$ that are linear homogeneous in the $22$ coordinates of $(\mathcal X,\mathcal Z,\eta,\xi)\in \mathbb S^4\times\mathbb S^4\times\mathbb R^2$, with coefficients in $\mathcal T_7$. → `LiftSpace` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/FunctionSpace.lean:58`)
- definition of the paper: Our lifting variable is a real linear functional $\Lambda:\mathcal E\to\mathbb R$; on vectors and matrices we apply it entrywise. → `LiftFunctional` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/FunctionSpace.lean:155`)
- definition of the paper: For an output point $(X,Z,y)$, impose \begin{equation}\label{eq:output} \Lambda(\mathcal X)=X,\qquad \Lambda(\mathcal Z)=Z,\qquad \Lambda\bigl(Y_\theta(\eta,\xi)\bigr)=y. \end{equation} → `OutputEquations` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/Moment.lean:51`)
- definition of the paper: We also require \begin{equation}\label{eq:moment} \Lambda\bigl(q(\theta)^T L_\theta(\mathcal X,\mathcal Z,\eta,\xi)q(\theta)\bigr)\geq0 \qquad\text{for every }q\in(\mathcal T_2)^{20}. \end{equation} → `MomentPositive` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/Moment.lean:114`)
- definition of the paper: Indeed, set $(f_1,\ldots,f_5)= (1,\cos\theta,\sin\theta,\cos2\theta,\sin2\theta)$ and define $H(\Lambda)\in\mathbb S^{100}$ by \begin{equation}\label{eq:moment-matrix} H(\Lambda)_{(i,a),(j,b)} =\Lambda\bigl(f_a f_b (L_\theta)_{ij}\bigr), \qquad 1\leq i,j\leq20,\quad 1\leq a,b\leq5. \end{equation} → `momentMatrixH` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/Moment.lean:75`)
- definition of the paper: Let $\mathcal T_j$ be the real vector space of trigonometric polynomials of degree at most $j$, with basis \[ 1,\cos\theta,\sin\theta,\ldots,\cos(j\theta),\sin(j\theta). \] → `IsTrigPolyLE` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:294`)
- definition of the paper: For a real column $r\in\R^3$ and a real vector $u=(u_0,u')\in\R\times\R^3$, define \begin{equation}\label{eq:BJ} B(r)=\begin{pmatrix}0&r^T\\-r&0_{3\times3}\end{pmatrix}, \qquad J_u=\begin{pmatrix}u'&-u_0I_3\end{pmatrix}. \end{equation} → `Bskew` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:190`)
- definition of the paper: If $r_1,\ldots,r_4$ are the columns of $\widetilde F_\theta(\eta,\xi)$, direct multiplication and Lemma~\ref{lem:gram} give \begin{equation}\label{eq:Phi-factor} \sum_{j=1}^4 B(r_j)^TWB(r_j) =\Phi_{Y_\theta(\eta,\xi)}(W) \qquad(W\in\Sym^4). \end{equation} → `phiFactorIdentity` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/Slice.lean:76`)
- definition of the paper: Consequently, for every $y\in\R^3$, \begin{equation}\label{eq:Phi-quadratic} u^T\Phi_y(W)u=\tr(J_uWJ_u^TQ(y)). \end{equation} → `phiQuadraticIdentity` (`lean/Papers/OaiExactSemidefiniteLift/Helpers/Slice.lean:104`)
- definition of the paper: Write \[ Q(y,z)=\tfrac12\bigl(Q(y+z)-Q(y)-Q(z)\bigr) \] for the symmetric bilinear polarization of $Q$, so that $Q(y,y)=Q(y)$. → `Qpol` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:275`)
- definition of the paper: For $S\in\mathbb S^3$ and $F,H\in\mathbb C^{3\times2}$, put \[ \langle F,H\rangle_S =\operatorname{Re}\operatorname{tr}(F^*SH) =\operatorname{tr}(\widetilde F^T S\widetilde H). \] → `weightedPairing` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:283`)
- definition of the paper: Write $\mathcal X,\mathcal Z\in\Sym^4$ for the matrix variables on a slice, and define \begin{equation}\label{eq:slice-pencil} L_\theta(\mathcal X,\mathcal Z,\eta,\xi) =\begin{pmatrix} I_4\otimes\mathcal X&\mathcal B_\theta(\eta,\xi)\\ \mathcal B_\theta(\eta,\xi)^T&\mathcal Z \end{pmatrix}, \qquad \mathcal B_\theta(\eta,\xi)= \begin{pmatrix}B(r_1)\\B(r_2)\\B(r_3)\\B(r_4)\end{pmatrix}. \end{equation} → `slicePencil` (`lean/Papers/OaiExactSemidefiniteLift/Basic.lean:258`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `sections/introduction.tex:68-79` | `Papers.OaiExactSemidefiniteLift.exact_semidefinite_lift` |
| Lemma 2.1 | `lem:gram` | `lem:gram` | `sections/angular.tex:32-40` | `Papers.OaiExactSemidefiniteLift.gram_identity` |
| Lemma 2.2 | `lem:slice` | `lem:slice` | `sections/slices.tex:51-63` | `Papers.OaiExactSemidefiniteLift.slice_equivalence` |
| Lemma 3.1 | `lem:matching` | `lem:matching` | `sections/matching.tex:29-42` | `Papers.OaiExactSemidefiniteLift.matching_exists` |
| Proposition 4.1 | `prop:lift` | `prop:lift` | `sections/lift.tex:57-65` | `Papers.OaiExactSemidefiniteLift.lift_equivalence` |

# The corrected paper and its Lean formalization — oai_smooth_nonquadratic_affine

For each result of the corrected paper: its statement, the Lean declaration that states it, whether that declaration is proved, and how the two statements correspond phrase by phrase. A result stated differently from the original paper is marked "corrected"; the report says what changed and why.

## Theorem 1.1

**Statement.** \label{thm:main} There exists a nonquadratic function $u\in C^\infty(\R^{10})$ with $D^2u$ positive definite at every point such that \[ \sum_{i,j=1}^{10}U^{ij}\partial_{ij} (\det D^2u)^{-11/12}=0 \quad\hbox{on }\R^{10}, \qquad U=\det(D^2u)(D^2u)^{-1}. \]

**Lean.** `OaiSmoothNonquadraticAffine.exists_nonquadratic_entire_affine_maximal` — `lean/Papers/OaiSmoothNonquadraticAffine/TMain.lean:362`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There exists a nonquadratic function $u\in C^\infty(\R^{10})$ with $D^2u$ positive definite at every point such that | then `∃ u : EuclideanSpace ℝ (Fin 10) → ℝ,`<br>then `ContDiff ℝ ∞ u`<br>then `¬ IsQuadraticFunction u`<br>then `HessianPositive u Set.univ` |
| \[ \sum_{i,j=1}^{10}U^{ij}\partial_{ij} (\det D^2u)^{-11/12}=0 \quad\hbox{on }\R^{10}, \qquad | `∀ z`<br>then `∑ i : Fin 10, ∑ j : Fin 10, (hessianMatrix u z).adjugate i j * hessianMatrix (fun z' => (hessianMatrix u z').det ^ (-(11 / 12 : ℝ))) z i j = 0` |
| U=\det(D^2u)(D^2u)^{-1}. \] | then `∑ i : Fin 10, ∑ j : Fin 10, (hessianMatrix u z).adjugate i j * hessianMatrix (fun z' => (hessianMatrix u z').det ^ (-(11 / 12 : ℝ))) z i j = 0` |

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For a smooth function $u:\R^n\to\R$ with positive definite Hessian, write \begin{equation}\label{eq:affine} \sum_{i,j=1}^n U^{ij}w_{ij}=0,\qquad U^{ij}=\det(D^2u)(D^2u)^{-1}_{ij},\qquad w=(\det D^2u)^{-(n+1)/(n+2)}. \end{equation} → `AffineMaximalEquation` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:108`)
- definition of the paper: Throughout this paper, positivity of the Hessian means pointwise positive definiteness, not a global lower bound by a fixed positive matrix. → `HessianPositive` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:72`)
- definition of the paper: From now on fix \begin{equation}\label{eq:constants} m=9,\qquad k=11,\qquad \gamma=12/11. \end{equation} → `radialGamma` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:208`)
- definition of the paper: We now take $F$ and $P$ radial, and use the same letters for their profiles in $r=|x|$. → `radialExtension` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:172`)
- definition of the paper: \begin{equation}\label{eq:radial} y^{m-1}y'=r^{m-1}FP^{-\gamma},\qquad (y^{m-1}P')'=-k r^{m-1}P^{1-\gamma},\qquad F'=y. \end{equation} → `RadialSystem` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:194`)
- definition of the paper: Write primes for radial derivatives and $y=F'$. → `radialY` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:178`)

## Proposition 2.1

**Statement.** \label{prop:reduction} Let $F,P$ be positive smooth functions on an open set $\Omega\subset\R^m$, and suppose $H=D_x^2F$ is positive definite. If \begin{equation}\label{eq:reduced} \det H=FP^{-\gamma},\qquad \tr(H^{-1}D_x^2P)+kP/F=0, \end{equation} then \[ u(x,t)=\sqrt{F(x)^2+t^2} \] has positive definite Hessian on $\Omega\times\R$ and satisfies \eqref{eq:affine} in dimension $n=m+1$.

**Lean.** `OaiSmoothNonquadraticAffine.reduction_affineMaximal` — `lean/Papers/OaiSmoothNonquadraticAffine/TReduction.lean:271`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| Let $F,P$ be positive smooth functions on an open set $\Omega\subset\R^m$, | `m : ℕ`<br>`Ω : Set (EuclideanSpace ℝ (Fin m))`<br>`F P : EuclideanSpace ℝ (Fin m) → ℝ`<br>`hFP : ReductionFunctions Ω F P` |
| and suppose $H=D_x^2F$ is positive definite. | `hH : ReductionHessianPosDef Ω F` |
| If \begin{equation} \det H=FP^{-\gamma},\qquad | `hSystem : ReducedSystem m Ω F P` |
| \tr(H^{-1}D_x^2P)+kP/F=0, \end{equation} | `hSystem : ReducedSystem m Ω F P` |
| then \[ u(x,t)=\sqrt{F(x)^2+t^2} \] | then `HessianPositive (reductionGraph F) {z | xPart z ∈ Ω}`<br>then `AffineMaximalEquation (m + 1) (reductionGraph F) {z | xPart z ∈ Ω}` |
| has positive definite Hessian on $\Omega\times\R$ and satisfies \eqref{eq:affine} in dimension $n=m+1$. | then `HessianPositive (reductionGraph F) {z | xPart z ∈ Ω}`<br>then `AffineMaximalEquation (m + 1) (reductionGraph F) {z | xPart z ∈ Ω}` |

Lean assumes conditions that the paper's text does not state: `hm : ReductionDimension m`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: For a smooth function $u:\R^n\to\R$ with positive definite Hessian, write \begin{equation}\label{eq:affine} \sum_{i,j=1}^n U^{ij}w_{ij}=0,\qquad U^{ij}=\det(D^2u)(D^2u)^{-1}_{ij},\qquad w=(\det D^2u)^{-(n+1)/(n+2)}. \end{equation} → `AffineMaximalEquation` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:108`)
- definition of the paper: Throughout this paper, positivity of the Hessian means pointwise positive definiteness, not a global lower bound by a fixed positive matrix. → `HessianPositive` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:72`)
- definition of the paper: Set \[ k=m+2,\qquad \gamma=\frac{m+3}{m+2}. \] → `reductionGamma` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:118`)
- condition of the paper: For this section let $m\geq1$ → `ReductionDimension` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:124`)
- condition of the paper: Let $F,P$ be positive smooth functions on an open set $\Omega\subset\R^m$ → `ReductionFunctions` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:132`)
- condition of the paper: suppose $H=D_x^2F$ is positive definite. → `ReductionHessianPosDef` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:143`)
- condition of the paper: If \begin{equation}\label{eq:reduced} \det H=FP^{-\gamma},\qquad \tr(H^{-1}D_x^2P)+kP/F=0, \end{equation} → `ReducedSystem` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:153`)

## Lemma 3.1

**Statement.** \label{lem:local} There is $\varepsilon>0$ and a solution $F,P$ of \eqref{eq:radial} on $0<r<\varepsilon$ such that $F(|x|)$ and $P(|x|)$ extend smoothly to $|x|<\varepsilon$, with \[ F(0)=P(0)=1,\qquad D_x^2F(0)=I,\qquad D_x^2P(0)=-\frac{11}{9}I. \] Moreover $F,P,y,y'>0$ and $P'<0$ for $0<r<\varepsilon$.

**Lean.** `OaiSmoothNonquadraticAffine.exists_local_radial_solution` — `lean/Papers/OaiSmoothNonquadraticAffine/Helpers/Local.lean:20`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| There is $\varepsilon>0$ and a solution $F,P$ of \eqref{eq:radial} on $0<r<\varepsilon$ such that $F(\|x\|)$ and $P(\|x\|)$ extend smoothly to $\|x\|<\varepsilon$, | then `∃ ε : ℝ,`<br>then `0 < ε`<br>then `∃ F P : ℝ → ℝ, LocalSolutionData ε F P` |
| with \[ F(0)=P(0)=1,\qquad | then `∃ F P : ℝ → ℝ, LocalSolutionData ε F P` |
| D_x^2F(0)=I,\qquad | then `∃ F P : ℝ → ℝ, LocalSolutionData ε F P` |
| D_x^2P(0)=-\frac{11}{9}I. \] | then `∃ F P : ℝ → ℝ, LocalSolutionData ε F P` |
| Moreover $F,P,y,y'>0$ | then `∃ F P : ℝ → ℝ, LocalSolutionData ε F P` |
| and $P'<0$ for $0<r<\varepsilon$. | then `∃ F P : ℝ → ℝ, LocalSolutionData ε F P` |

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: We now take $F$ and $P$ radial, and use the same letters for their profiles in $r=|x|$. → `radialExtension` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:172`)
- definition of the paper: \begin{equation}\label{eq:radial} y^{m-1}y'=r^{m-1}FP^{-\gamma},\qquad (y^{m-1}P')'=-k r^{m-1}P^{1-\gamma},\qquad F'=y. \end{equation} → `RadialSystem` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:194`)
- definition of the paper: From now on fix \begin{equation}\label{eq:constants} m=9,\qquad k=11,\qquad \gamma=12/11. \end{equation} → `radialGamma` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:208`)
- definition of the paper: Write primes for radial derivatives and $y=F'$. → `radialY` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:178`)

## Lemma 4.1

**Statement.** \label{lem:autonomous} On the interval of continuation, $A,B>0$, and the functions $A,B,D$ satisfy \begin{equation}\label{eq:autonomous} \begin{aligned} \dot A&=A(1+B-A),\\ \dot B&=B\bigl(9+A+(12/11)BD-9B\bigr),\\ \dot D&=(11-D)A-8D+BD(1-D/11). \end{aligned} \end{equation} Moreover $(A,B,D)\to(0,1,0)$ as $r\downarrow0$, and all three coordinates are positive for sufficiently small $r>0$.

**Lean.** `OaiSmoothNonquadraticAffine.autonomous_system_of_continuation` — `lean/Papers/OaiSmoothNonquadraticAffine/Helpers/Autonomous.lean:333`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| On the interval of continuation, $A,B>0$, | `hCont : IsMaximalContinuation F₀ P₀ ε F P R`<br>`∀ r ∈ radialInterval R`<br>then `0 < radialCoordinates F P r 0`<br>then `0 < radialCoordinates F P r 1` |
| and the functions $A,B,D$ satisfy | then `HasDerivAt (fun τ => radialCoordinates F P (Real.exp τ)) (autonomousField (radialCoordinates F P r)) (Real.log r)` |
| \begin{equation} \begin{aligned} \dot A&=A(1+B-A),\\ \dot B&=B\bigl(9+A+(12/11)BD-9B\bigr),\\ \dot D&=(11-D)A-8D+BD(1-D/11). \end{aligned} \end{equation} | then `HasDerivAt (fun τ => radialCoordinates F P (Real.exp τ)) (autonomousField (radialCoordinates F P r)) (Real.log r)` |
| Moreover $(A,B,D)\to(0,1,0)$ as $r\downarrow0$, | then `Tendsto (radialCoordinates F P) (𝓝[>] 0) (𝓝 (![0, 1, 0] : Fin 3 → ℝ))` |
| and all three coordinates are positive for sufficiently small $r>0$. | then `∀ᶠ r in 𝓝[>] (0 : ℝ),`<br>then `0 < radialCoordinates F P r 0`<br>then `0 < radialCoordinates F P r 1`<br>then `0 < radialCoordinates F P r 2` |

Lean also declares what the paper leaves implicit (the objects and their types): `ε : ℝ`, `F₀ P₀ F P : ℝ → ℝ`, `R : WithTop ℝ`.

Lean assumes conditions that the paper's text does not state: `hLocal : LocalSolutionData ε F₀ P₀`.

Lean concludes what the paper's text does not state: `RadialCoordinateDomain F P r`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: \begin{equation}\label{eq:radial} y^{m-1}y'=r^{m-1}FP^{-\gamma},\qquad (y^{m-1}P')'=-k r^{m-1}P^{1-\gamma},\qquad F'=y. \end{equation} → `RadialSystem` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:194`)
- definition of the paper: From now on fix \begin{equation}\label{eq:constants} m=9,\qquad k=11,\qquad \gamma=12/11. \end{equation} → `radialGamma` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:208`)
- definition of the paper: Take the maximal outward continuation of the local solution on which $F,P,y>0$. → `IsMaximalContinuation` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:254`)
- definition of the paper: Explicitly, with $Z=P'$ and \[ G(r,F,P,y)=\frac{r^8FP^{-12/11}}{y^8}, \] it reads \begin{equation}\label{eq:regular} F'=y,\qquad P'=Z,\qquad y'=G,\qquad Z'=-8\frac Gy Z-\frac{11r^8P^{-1/11}}{y^8}. \end{equation} → `regularField` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:278`)
- definition of the paper: \begin{equation}\label{eq:ratios} A=\frac{ry}{F},\qquad B=\frac{ry'}y, \qquad C=-\frac{rP'}P, \end{equation} → `ratioA` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:286`)
- definition of the paper: and let a dot mean differentiation with respect to $\log r$. → `logTimeDeriv` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:332`)
- definition of the paper: Since $B>0$, we may also set $D=C/B$. → `ratioD` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:305`)
- definition of the paper: Write primes for radial derivatives and $y=F'$. → `radialY` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:178`)

## Lemma 4.2

**Statement.** \label{lem:box} The box \begin{equation}\label{eq:box} \mathcal B=[0,9/2]\times[0,7/2]\times[0,33/7] \end{equation} is forward invariant for \eqref{eq:autonomous}. The solution arising from Lemma~\ref{lem:local} lies in $\mathcal B$ throughout its interval of continuation.

**Lean.** `OaiSmoothNonquadraticAffine.box_forward_invariant` — `lean/Papers/OaiSmoothNonquadraticAffine/Helpers/Box.lean:23`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| The box \begin{equation} \mathcal B=[0,9/2]\times[0,7/2]\times[0,33/7] \end{equation} | `z a ∈ boxB`<br>then `z τ ∈ boxB`<br>then `radialCoordinates F P r ∈ boxB` |
| is forward invariant for \eqref{eq:autonomous}. | `a ≤ b`<br>`∀ τ ∈ Ico a b`<br>`HasDerivAt z (autonomousField (z τ)) τ`<br>`z a ∈ boxB`<br>`∀ τ ∈ Icc a b`<br>then `z τ ∈ boxB` |
| The solution arising from Lemma~\ref{lem:local} lies in $\mathcal B$ throughout its interval of continuation. | `LocalSolutionData ε F₀ P₀`<br>`IsMaximalContinuation F₀ P₀ ε F P R`<br>`∀ r ∈ radialInterval R`<br>then `radialCoordinates F P r ∈ boxB` |

Lean also declares what the paper leaves implicit (the objects and their types): `z : ℝ → Fin 3 → ℝ`, `a b : ℝ`, `ε : ℝ`, `F₀ P₀ F P : ℝ → ℝ`, `R : WithTop ℝ`.

Lean assumes conditions that the paper's text does not state: `ContinuousOn z (Icc a b)`.

Lean concludes what the paper's text does not state: `RadialCoordinateDomain F P r`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: Take the maximal outward continuation of the local solution on which $F,P,y>0$. → `IsMaximalContinuation` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:254`)
- definition of the paper: \begin{equation}\label{eq:ratios} A=\frac{ry}{F},\qquad B=\frac{ry'}y, \qquad C=-\frac{rP'}P, \end{equation} → `ratioA` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:286`)
- definition of the paper: and let a dot mean differentiation with respect to $\log r$. → `logTimeDeriv` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:332`)
- definition of the paper: Since $B>0$, we may also set $D=C/B$. → `ratioD` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:305`)

## Proposition 4.3

**Statement.** \label{prop:global} The solution in Lemma~\ref{lem:local} extends to every $r>0$, with $F,P,y,y'>0$. Its radial extensions to $\R^9$ are smooth, and $D_x^2F$ is positive definite everywhere.

**Lean.** `OaiSmoothNonquadraticAffine.local_radial_solution_extends_globally` — `lean/Papers/OaiSmoothNonquadraticAffine/TGlobal.lean:24`

**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice, Quot.sound).

**Statement correspondence.**

| The paper says | Lean states |
| --- | --- |
| The solution in Lemma~\ref{lem:local} extends to every $r>0$, | `hLocal : LocalSolutionData ε F₀ P₀`<br>then `∃ F P : ℝ → ℝ,`<br>`∀ r ∈ Ico 0 ε`<br>then `F r = F₀ r`<br>then `P r = P₀ r`<br>then `RadialSystem radialDim radialK radialGamma F P (Ioi 0)`<br>`∀ r > 0` |
| with $F,P,y,y'>0$. | then `0 < F r`<br>then `0 < P r`<br>then `0 < deriv F r`<br>then `0 < deriv (deriv F) r` |
| Its radial extensions to $\R^9$ are smooth, | then `ContDiff ℝ ∞ (radialExtension 9 F)`<br>then `ContDiff ℝ ∞ (radialExtension 9 P)` |
| and $D_x^2F$ is positive definite everywhere. | `∀ x`<br>then `(hessianMatrix (radialExtension 9 F) x).PosDef` |

Lean also declares what the paper leaves implicit (the objects and their types): `ε : ℝ`, `F₀ P₀ : ℝ → ℝ`.

**Conditions and readings, and the Lean definitions that carry them.**

- definition of the paper: We now take $F$ and $P$ radial, and use the same letters for their profiles in $r=|x|$. → `radialExtension` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:172`)
- definition of the paper: From now on fix \begin{equation}\label{eq:constants} m=9,\qquad k=11,\qquad \gamma=12/11. \end{equation} → `radialGamma` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:208`)
- definition of the paper: Take the maximal outward continuation of the local solution on which $F,P,y>0$. → `IsMaximalContinuation` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:254`)
- definition of the paper: Explicitly, with $Z=P'$ and \[ G(r,F,P,y)=\frac{r^8FP^{-12/11}}{y^8}, \] it reads \begin{equation}\label{eq:regular} F'=y,\qquad P'=Z,\qquad y'=G,\qquad Z'=-8\frac Gy Z-\frac{11r^8P^{-1/11}}{y^8}. \end{equation} → `regularField` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:278`)
- definition of the paper: \begin{equation}\label{eq:ratios} A=\frac{ry}{F},\qquad B=\frac{ry'}y, \qquad C=-\frac{rP'}P, \end{equation} → `ratioA` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:286`)
- definition of the paper: Since $B>0$, we may also set $D=C/B$. → `ratioD` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:305`)
- definition of the paper: Write primes for radial derivatives and $y=F'$. → `radialY` (`lean/Papers/OaiSmoothNonquadraticAffine/Basic.lean:178`)

## Identifiers

| Result | run id | paper label | source | Lean declaration |
| --- | --- | --- | --- | --- |
| Theorem 1.1 | `thm:main` | `thm:main` | `main.tex:53-62` | `OaiSmoothNonquadraticAffine.exists_nonquadratic_entire_affine_maximal` |
| Proposition 2.1 | `prop:reduction` | `prop:reduction` | `main.tex:123-137` | `OaiSmoothNonquadraticAffine.reduction_affineMaximal` |
| Lemma 3.1 | `lem:local` | `lem:local` | `main.tex:220-230` | `OaiSmoothNonquadraticAffine.exists_local_radial_solution` |
| Lemma 4.1 | `lem:autonomous` | `lem:autonomous` | `main.tex:328-340` | `OaiSmoothNonquadraticAffine.autonomous_system_of_continuation` |
| Lemma 4.2 | `lem:box` | `lem:box` | `main.tex:378-386` | `OaiSmoothNonquadraticAffine.box_forward_invariant` |
| Proposition 4.3 | `prop:global` | `prop:global` | `main.tex:429-433` | `OaiSmoothNonquadraticAffine.local_radial_solution_extends_globally` |

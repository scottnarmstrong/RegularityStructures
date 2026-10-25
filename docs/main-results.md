# The 20 main results proved in this formalization

This page lists the 20 main results of this repository: Theorem A on the dynamical $`\Phi^4_3`$ model, with the
statements showing that its limit is well defined and that its hypotheses can be met (items 1 to 8), and the
theorems of the general theory of regularity structures that the library proves (items 9 to 20). Each link opens the
file with the exact Lean statement; each of these files states one theorem and names the theorem that proves it. The
same 20 declarations are the `main_results` of [`formalization.yaml`](../formalization.yaml), and
`scripts/check-axioms.py` checks their axioms.

Items 1 to 8 follow the numbering of the self-contained statement [`statement.pdf`](statement.pdf) (source
[`statement.tex`](statement.tex)), which defines every object they use. Items 9 to 20 cite
[Hai14] M. Hairer, *A theory of regularity structures*, Invent. Math. 198 (2014), numbered as in arXiv:1303.5113v4;
[Hos25] M. Hoshino, *A semigroup approach to the reconstruction theorem and the multilevel Schauder estimate*, Ann.
Henri Lebesgue 8 (2025), numbered as in arXiv:2310.07396v2; and [HS23] M. Hairer and R. Steele, *The BPHZ theorem for
regularity structures via the spectral gap inequality*, Arch. Ration. Mech. Anal. 248 (2024), numbered as in
arXiv:2301.10081v3. Where a statement differs from its source, the difference is recorded in
[`ERRATA-AND-DEVIATIONS.md`](ERRATA-AND-DEVIATIONS.md).

## Conventions

**The torus and the norm.** $`\mathbb T^3=\mathbb R^3/\mathbb Z^3`$ carries the probability Haar measure. On it,
$`p_t(x)=\sum_{k\in\mathbb Z^3}\gamma_t(x+k)`$ is the periodised heat kernel, where
$`\gamma_t(y)=(4\pi t)^{-3/2}e^{-\lvert y\rvert^2/4t}`$, and $`P_s`$ is convolution with $`\gamma_s`$. The massive
space-time heat kernel is $`G(t,x)=\mathbf 1_{t\gt0}\,e^{-t}p_t(x)`$. For $`\eta\lt0`$,

```math
\lVert f\rVert_\eta=\sup_{0\lt s\le1}s^{-\eta/2}\sup_{x\in\mathbb T^3}\lvert(P_sf)(x)\rvert,
```

and $`\mathcal C^\eta`$ is the completion of $`C(\mathbb T^3)`$ for this norm. It is equivalent to the Littlewood–Paley
norm of $`B^\eta_{\infty,\infty}(\mathbb T^3)`$
([`Statements.closureNorm_equiv_littlewoodPaley`](../Phi43Statements/Steps/ClosureNormEquiv.lean)).

**White noise and the regularised noise.** A space-time white noise is a family $`(W(h))_{h\in L^2(\mathbb R\times\mathbb T^3)}`$
of random variables whose finite subfamilies are centred Gaussian vectors with covariance
$`\mathbb E[W(h)W(g)]=\langle h,g\rangle`$. A mollifier is $`\rho\in C_c^\infty(\mathbb R\times\mathbb R^3)`$ with
$`\int\rho=1`$; no symmetry is assumed. With $`\rho_\varepsilon(t,x)=\varepsilon^{-5}\rho(\varepsilon^{-2}t,\varepsilon^{-1}x)`$
and its spatial periodisation $`\rho_\varepsilon^\sharp`$, a regularised noise is a field $`\xi_\varepsilon(\omega,z)`$,
smooth in $`z`$ for every $`\omega`$, equal almost surely, at each $`z`$, to $`W(\rho_\varepsilon^\sharp(z-\cdot))`$.

**The constants.** With $`G_\varepsilon=G*\rho_\varepsilon^\sharp`$ and $`Q_\varepsilon(z)=\int G_\varepsilon(z+w)G_\varepsilon(w)\,dw`$,

```math
C_1^\varepsilon=\int_{\mathbb R\times\mathbb T^3}G_\varepsilon(z)^2\,dz,\qquad C_2^\varepsilon=2\int_{\mathbb R\times\mathbb T^3}G(z)\,Q_\varepsilon(z)^2\,dz .
```

These are Hairer's constants (10.33) and (10.41) with the massive kernel $`G`$ in place of his truncated kernel; the
differences converge to limits that do not depend on the mollifier
([`Statements.constantsComparison`](../Phi43Statements/Steps/ConstantsComparison.lean)).

**Classical solutions.** For smooth $`f`$ on $`\mathbb R\times\mathbb T^3`$, $`c\in\mathbb R`$ and smooth $`u_0`$, a classical
solution of $`\partial_tu=\Delta u-u^3+cu+f`$, $`u(0)=u_0`$, is a continuous function on $`[0,\infty)\times\mathbb T^3`$,
smooth on $`(0,\infty)\times\mathbb T^3`$, solving the equation there; it is recorded as a path
$`t\mapsto u(t)\in C(\mathbb T^3)`$. In items 1 and 2, $`u_\varepsilon(\omega)`$ is the classical solution of

```math
\partial_tu_\varepsilon=\Delta u_\varepsilon-u_\varepsilon^3+\bigl(a+3C_1^\varepsilon-9C_2^\varepsilon\bigr)u_\varepsilon+\xi_\varepsilon(\omega),\qquad u_\varepsilon(0)=u_0,
```

for $`0\lt\varepsilon\le1`$, with $`a\in\mathbb R`$ and $`u_0`$ smooth.

| Group | Lean definitions | File |
| --- | --- | --- |
| Torus and space-time (namespace `RegularityStructures`) | `Torus3`, `SpaceTime`, `torusProj`, `torusRep`, `sqNorm3`, `IsSmoothOnTorus`, `IsSmoothOnSpaceTime` | [`Torus/Basic.lean`](../RegularityStructures/Torus/Basic.lean) |
| Heat kernels | `gaussKernel`, `heatKernel`, `heatSemigroup`, `massiveHeatKernel` | [`Torus/HeatKernel.lean`](../RegularityStructures/Torus/HeatKernel.lean) |
| The space $`\mathcal C^\eta`$ | `NegExponent`, `holderBesovENorm`, `holderBesovSeminorm`, `HolderBesovPre`, `HolderBesov`, `toHolderBesov` | [`Torus/HolderBesov.lean`](../RegularityStructures/Torus/HolderBesov.lean) |
| White noise | `IsCentredGaussianVector`, `IsWhiteNoise` | [`Probability/WhiteNoise.lean`](../RegularityStructures/Probability/WhiteNoise.lean) |
| Mollifiers and regularised noise (namespace `RegularityStructures.Phi43`) | `IsMollifier`, `rescale`, `periodise`, `mollifierAt`, `IsRegularisedNoise` | [`Phi43/Mollifier.lean`](../Phi43/Mollifier.lean) |
| Constants | `mollifiedKernel`, `covariance`, `wickConstant`, `sunsetConstant` | [`Phi43/Constants.lean`](../Phi43/Constants.lean) |
| Solutions and the limit | `IsClassicalSolution`, `IsPhi43Limit` | [`Phi43/ClassicalSolution.lean`](../Phi43/ClassicalSolution.lean), [`Phi43/Limit.lean`](../Phi43/Limit.lean) |

**The general theory.** The library [`RegularityStructures/`](../RegularityStructures/) does not depend on
[`Phi43/`](../Phi43/). A *regularity structure* is recorded through a finite graded basis: an index type $`\iota`$ with
degrees, the model space $`T=\mathbb R^\iota`$, and a structure group of graded unipotent maps. A *regularising
semigroup* is a family of kernels $`Q_t(x,y)`$ on a measure space with the semigroup property and moment bounds of
scaling order $`\ell`$ ([Hos25, Definition 2.6]); its *distributions* are the families $`(\Lambda_t)_{t\gt0}`$ with
$`Q_s\Lambda_t=\Lambda_{s+t}`$, the regularisations of a distribution. A *model* is a pair $`(\Pi,\Gamma)`$ with
$`\Pi_x\colon T\to`$ distributions and $`\Pi_x\Gamma_{xy}=\Pi_y`$; its bounds $`\lVert\Pi\rVert\le C_\Pi`$ and
$`\lVert\Gamma\rVert\le C_\Gamma`$ are hypotheses with explicit constants. $`D^\gamma`$ is the space of modelled
distributions, and $`\lVert f\rVert\le C_f`$ its bound; all model and $`D^\gamma`$ bounds are global, on the whole
space, whereas Hairer's are on compact sets. $`Rf`$ is the semigroup reconstruction of the germ $`y\mapsto\Pi_yf(y)`$.
On $`\mathbb R^4=\mathbb R\times\mathbb R^3`$ with parabolic scaling, the parabolic heat semigroup regularises
distributions, and $`B^r`$ is the class of smooth test functions vanishing outside the unit parabolic ball with
derivatives of order at most $`r`$ bounded by one; $`\varphi^\lambda_x`$ is $`\varphi`$ rescaled by $`\lambda`$ and centred
at $`x`$.

| Group | Lean definitions (namespace `RegularityStructures`) |
| --- | --- |
| Structures | [`RegularityStructure`](../RegularityStructures/Abstract/RegularityStructure.lean) |
| Semigroups | [`RegularisingSemigroup`, `RegularisingSemigroup.distributions`](../RegularityStructures/Analysis/Semigroup/Basic.lean) |
| Models | [`Model`, `Model.regPi`, `Model.PiBoundOn`, `Model.GammaBoundOn`](../RegularityStructures/Abstract/Model.lean) |
| Modelled distributions | [`Model.modelledDistributions`, `Model.ModelledBoundOn`](../RegularityStructures/Abstract/ModelledDistribution.lean) |
| Reconstruction | [`Model.reconstruct`](../RegularityStructures/Abstract/Reconstruction.lean) |
| Parabolic semigroup and kernel | [`parabolicSemigroup`](../RegularityStructures/Analysis/Kernel/ParabolicSemigroup.lean), [`kConv`](../RegularityStructures/Abstract/Integration/Commute/KConvShell.lean) |
| Sectors and integration | [`RegularityStructure.IsSector`, `PolynomialSector`, `IsAbstractIntegration`](../RegularityStructures/Abstract/Integration.lean) |
| The Schauder operator | [`kGamma`](../RegularityStructures/Abstract/Integration/KGamma.lean) |
| Schauder hypotheses | [`SchauderSetting`, `SchauderNonIntegral`](../RegularityStructures/Abstract/Integration/Theorem512/Setting.lean) |

## The results

### Theorem A and its well-posedness

1. **[Theorem A](../Phi43Statements/TheoremA.lean)** (`theoremA`) — Let $`W`$ be a space-time white noise on a
   probability space, $`a\in\mathbb R`$, $`u_0`$ smooth on $`\mathbb T^3`$, $`-2/3\lt\eta\lt-1/2`$ and $`\rho`$ a mollifier,
   and let $`\xi_\varepsilon`$ and $`u_\varepsilon`$ be as in the conventions. Then there are a random time
   $`\tau\colon\Omega\to(0,\infty]`$ and, for each $`\omega`$, a continuous path $`u(\omega,\cdot)\colon[0,\tau(\omega))\to\mathcal C^\eta`$
   such that (A1) $`u(\omega,0)=u_0`$, and $`\omega\mapsto u(\omega,t)`$ is measurable on $`\{\tau\gt t\}`$; (A2) if
   $`\tau(\omega)\lt\infty`$, then $`\sup_{t\lt\tau(\omega)}\lVert u(\omega,t)\rVert_\eta=\infty`$; (A3) for all $`T,\delta\gt0`$,
   $`\lim_{\varepsilon\downarrow0}\mathbb P\bigl(\tau\gt T\ \text{and}\ \sup_{t\le T}\lVert u_\varepsilon(t)-u(t)\rVert_\eta\gt\delta\bigr)=0`$;
   and (A4) for every other mollifier $`\rho'`$, with regularised noises driven by the same $`W`$, every pair
   $`(\tau',u')`$ that satisfies (A1)–(A3) for $`\rho'`$ has $`\tau'=\tau`$ almost surely, and almost surely
   $`u'(t)=u(t)`$ for all $`t\lt\tau`$. The probability in (A3) is read as an outer measure (convention (D7) of the
   statement). ([Hai14, Theorem 1.15], with smooth initial data and explicit constants; Theorem A of the statement.)

2. **[Uniqueness of the limit](../Phi43Statements/Proposition31.lean)** (`proposition31`) — For given solutions
   $`u_\varepsilon`$, two pairs $`(\tau,u)`$ and $`(\tau',u')`$ satisfying (A1)–(A3) have almost surely equal explosion
   times, and almost surely equal paths before them. So (A4) compares well-defined objects. (Proposition 3.1 of the
   statement.)

3. **[Existence of white noise](../Phi43Statements/WhiteNoiseExists.lean)** (`exists_whiteNoise`) — Some probability
   space carries a space-time white noise on $`\mathbb R\times\mathbb T^3`$. (Lemma 4.1 (W1) of the statement.)

4. **[Regularised noises](../Phi43Statements/RegularisedNoiseExistsUnique.lean)** (`regularisedNoise_exists_unique`) —
   For every white noise $`W`$ on a probability space, mollifier $`\rho`$ and $`0\lt\varepsilon\le1`$, a regularised noise
   at scale $`\varepsilon`$ exists; any two are indistinguishable; and every regularised noise is jointly measurable on
   $`\Omega\times(\mathbb R\times\mathbb T^3)`$. (Lemma 4.1 (W2) and Definition 2.4 of the statement.)

5. **[Finite constants](../Phi43Statements/ConstantsFinite.lean)** (`constants_finite`) — For every mollifier and
   $`0\lt\varepsilon\le1`$: $`G`$ is integrable; each $`\rho_\varepsilon^\sharp(z-\cdot)`$ is square-integrable; the integrals
   defining $`G_\varepsilon(z)`$ and $`Q_\varepsilon(z)`$ converge absolutely; $`G_\varepsilon`$ is continuous, integrable and
   bounded; $`Q_\varepsilon`$ is continuous and bounded; and $`G_\varepsilon^2`$ and $`G\,Q_\varepsilon^2`$ are integrable. So
   $`C_1^\varepsilon`$ and $`C_2^\varepsilon`$ are finite. (Lemma 4.1 (W3) and Definition 2.5 of the statement.)

6. **[Classical well-posedness](../Phi43Statements/ClassicalWellPosed.lean)** (`classicalSolution_exists_unique`) —
   For every $`c\in\mathbb R`$, smooth $`f`$ on $`\mathbb R\times\mathbb T^3`$ and smooth $`u_0`$, the equation
   $`\partial_tu=\Delta u-u^3+cu+f`$, $`u(0)=u_0`$, has a classical solution, and any two classical solutions agree at all
   times $`t\ge0`$. (Lemma 4.1 (W4) and Definition 2.6 of the statement.)

7. **[Continuous paths](../Phi43Statements/ClassicalSolutionContinuity.lean)** (`classicalSolution_continuousOn`) —
   For every $`\eta\lt0`$, every classical solution is a continuous path $`[0,\infty)\to\mathcal C^\eta`$. (Lemma 4.1 (W5),
   first half, of the statement.)

8. **[Measurable solutions](../Phi43Statements/ClassicalSolutionMeasurability.lean)** (`classicalSolution_measurable`)
   — If $`\xi`$ is a regularised noise at scale $`0\lt\varepsilon\le1`$ of a white noise on a probability space and
   $`u(\omega)`$ is the classical solution driven by $`\xi(\omega)`$, for a constant $`c`$ and smooth $`u_0`$, then for every
   $`\eta\lt0`$ and $`t\ge0`$ the map $`\omega\mapsto u(\omega,t)\in\mathcal C^\eta`$ is measurable. (Lemma 4.1 (W5), second
   half, of the statement.)

### Reconstruction

In items 9 to 12 the regularity structure has a finite graded basis, the measure of the underlying space is
$`s`$-finite, and the constants $`c`$ depend only on the structure, the semigroup and $`\gamma`$.

9. **[The reconstruction theorem](../RegularityStructures/Statements/ModelReconstruction.lean)**
   (`Statements.Model.exists_reconstruction`) — For $`\gamma\gt0`$ there is $`c`$ such that for every model with
   $`\lVert\Pi\rVert\le C_\Pi`$ and every $`f\in D^\gamma`$ with $`\lVert f\rVert\le C_f`$, the reconstruction $`Rf`$ is a
   distribution with $`\lvert Q_t(Rf-\Pi_xf(x))(x)\rvert\le c\,C_\Pi C_f\,t^{\gamma/\ell}`$ for $`0\lt t\le1`$, and it is the only
   distribution with a bound of this form. ([Hai14, Theorem 3.10]; [Hos25, Theorem 4.1].)

10. **[Continuity in the model](../RegularityStructures/Statements/ModelReconstructionLipschitz.lean)**
    (`Statements.Model.abs_reconstruct_sub_reconstruct_le`) — For $`\gamma\gt0`$, two models with
    $`\lVert\Pi^1\rVert\le C_{\Pi^1}`$, $`\lVert\Pi^2\rVert\le C_{\Pi^2}`$ and $`\lVert\Pi^1-\Pi^2\rVert\le C_{\delta\Pi}`$, and
    $`f^i\in D^\gamma`$ for the model $`i`$ with $`\lVert f^i\rVert\le C_{f^i}`$ and $`\lVert f^1;f^2\rVert\le C_{\delta f}`$
    ([Hai14, (3.2)]):
    $`\lvert Q_t(R^1f^1-\Pi^1_xf^1(x)-R^2f^2+\Pi^2_xf^2(x))(x)\rvert\le c\,(C_{f^1}C_{\delta\Pi}+C_{\delta f}C_{\Pi^2})\,t^{\gamma/\ell}`$
    for $`0\lt t\le1`$. ([Hai14, Theorem 3.10, (3.4)]; [Hos25, Theorem 4.1].)

11. **[The bound (3.3) for test functions](../RegularityStructures/Statements/ReconstructionTestFunctionBound.lean)**
    (`Statements.Model.abs_pairing_rescaledTestFunction_le`) — On $`\mathbb R^4`$ with the parabolic heat semigroup, if
    $`\gamma\gt0`$ and every degree of the structure below $`\gamma`$ exceeds $`-4`$, then for every model and $`f`$ as in
    item 9, every $`\varphi\in B^4`$, $`0\lt\lambda\le1`$ and $`x`$, the pairing $`\langle Rf-\Pi_xf(x),\varphi^\lambda_x\rangle`$ exists (as
    the limit of the pairings of the regularisations) and is at most $`c\,C_\Pi C_f\lambda^\gamma`$ in absolute value.
    ([Hai14, Theorem 3.10, (3.3)].)

12. **[Uniqueness for test functions](../RegularityStructures/Statements/ReconstructionUniqueness.lean)**
    (`Statements.Model.eq_reconstruct_of_abs_pairing_le`) — Under the hypotheses of item 11, let $`\Lambda`$ be a
    distribution whose regularisations $`\Lambda_u`$ are measurable and satisfy
    $`\lvert\Lambda_u\rvert\le C\,u^{\alpha/4}`$ for $`0\lt u\le1`$, for some $`\alpha\gt-4`$. If
    $`\lvert\langle\Lambda-\Pi_xf(x),\varphi^\lambda_x\rangle\rvert\le C'\lambda^\gamma`$ for all $`0\lt\lambda\le1`$ and $`x`$, for one
    $`\varphi\in B^4`$ with $`\int\varphi\ne0`$, then $`\Lambda=Rf`$. ([Hai14, Theorem 3.10], uniqueness.)

13. **[Reconstruction for coherent germs](../RegularityStructures/Statements/GermReconstruction.lean)**
    (`Statements.RegularisingSemigroup.exists_reconstruction`) — For a regularising semigroup on an $`s`$-finite measure
    space, $`\gamma\gt0`$ and a finite set $`A`$ of exponents below $`\gamma`$, there is $`c`$ such that every germ $`F`$ that
    is coherent of order $`\gamma`$ with exponents $`A`$ and constant $`C`$, that is,
    $`\lvert Q_t(F_y-F_z)(z)\rvert\le C\sum_{a\in A}t^{a/\ell}d(z,y)^{\gamma-a}`$ for $`0\lt t\le1`$, has a reconstruction
    $`RF`$ with $`\lvert(RF)_t(x)-(Q_tF_x)(x)\rvert\le c\,C\,t^{\gamma/\ell}`$ for $`0\lt t\le1`$, and $`RF`$ is the only distribution with a bound
    of this form. ([Hos25, Theorem 4.1].)

14. **[Weighted reconstruction](../RegularityStructures/Statements/WeightedReconstruction.lean)**
    (`Statements.RegularisingSemigroup.exists_reconstruction_weighted`) — The same, with a polynomially moderate weight
    $`w\ge1`$, $`w(z)\le w(y)(1+d(z,y))^p`$: every weighted coherent germ has a reconstruction with
    $`\lvert(RF)_t(x)-(Q_tF_x)(x)\rvert\le c\,C\,w(x)\,t^{\gamma/\ell}`$, where $`c`$ is chosen before the germ and the weight, and $`RF`$
    is the only distribution with a bound of this form. ([Hos25, Theorem 4.1], with a weight.)

### The multilevel Schauder estimate

In items 15 and 16, on $`\mathbb R^4`$ with parabolic scaling, $`K=\sum_nK_n`$ is the singular part of the heat kernel and
$`\mathcal K_\gamma f=If+Jf+N_\gamma f`$ ([Hai14, (5.15)]). The standing hypotheses (`SchauderSetting`) are: $`\gamma\gt0`$;
the model realises $`K`$ for the abstract integration map $`I`$ of order two ([Hai14, Definition 5.7]) on the sector $`V`$;
$`V`$ is a coordinate sector (whenever an element of $`V`$ has a nonzero coordinate $`j`$, the basis vector $`e_j`$ lies in
$`V`$); every degree of the structure below $`\gamma`$ exceeds $`-2`$, which excludes the noise symbol of the $`\Phi^4_3`$
structure; enough abstract polynomials are present; $`I`$ has no component along the polynomials; and the model bounds
$`\lVert\Pi\rVert\le C_\Pi`$, $`\lVert\Gamma\rVert\le C_\Gamma`$ and the bound $`C_I`$ of $`I`$ hold globally. The non-integrality
conditions on $`\gamma`$ (`SchauderNonIntegral`) can be stronger than Hairer's. Both results assume that the model is
jointly measurable. Only the first part of [Hai14, Theorem 5.12] is stated, not the local Lipschitz estimate in the
model.

15. **[The multilevel Schauder estimate](../RegularityStructures/Statements/SchauderEstimate.lean)**
    (`Statements.Model.kGamma_mem_modelledDistributions`) — There is $`c\ge0`$, depending only on the structure, $`\gamma`$
    and the annihilation order, such that for every model satisfying the standing hypotheses and every $`f\in D^\gamma`$
    with values in $`V`$ and $`\lVert f\rVert\le C_f`$: $`\mathcal K_\gamma f\in D^{\gamma+2}`$, with the bound
    $`c\cdot\max(1,C_I)\max(1,C_\Pi)\max(C_\Gamma,1)\,C_f`$. ([Hai14, Theorem 5.12], first part.)

16. **[Reconstruction of $`\mathcal K_\gamma f`$](../RegularityStructures/Statements/SchauderReconstruction.lean)**
    (`Statements.Model.reconstruct_kGamma`) — If, in addition, $`\gamma+2`$ is not a parabolic degree and the model
    satisfies a global bound on $`\Pi`$ up to level $`\gamma+2`$, then $`R\mathcal K_\gamma f=K*Rf`$: its regularisations are
    $`Q_t(K*Rf)`$ for $`t\gt0`$. ([Hai14, Theorem 5.12, (5.17)].)

### Maximal solutions and Malliavin calculus

17. **[Maximal solutions and the blow-up alternative](../RegularityStructures/Statements/MaximalSolution.lean)**
    (`Statements.exists_maximal_solution`) — Let a solution relation on a state space with a size function satisfy:
    solutions depend only on their values on $`[0,T]`$; restriction to shorter times; local uniqueness; local existence
    for a time depending only on the size of the datum; and gluing at a restart time. Then every datum has a solution on
    $`[0,T^*)`$, $`T^*\in(0,\infty]`$, that extends every other solution, and if $`T^*\lt\infty`$ the size of the solution
    tends to infinity at $`T^*`$. This is the patching argument behind [Hai14, Proposition 7.11] and the discussion
    after it, not Proposition 7.11 itself; the hypotheses must be checked for each equation.

18. **[Global solutions under an a priori bound](../RegularityStructures/Statements/GlobalSolution.lean)**
    (`Statements.exists_global_solution_of_bound`) — Under the hypotheses of item 17, if the size of every solution
    stays below a fixed bound, the maximal solution exists for all times.

19. **[Closability of the Malliavin derivative](../RegularityStructures/Statements/MalliavinClosable.lean)**
    (`Statements.malliavin_derivative_closable`) — For a white noise $`W`$ on a probability space, if cylindrical
    functionals $`F_n`$ converge to $`0`$ in $`L^2`$ and their derivatives $`DF_n`$ converge to $`G`$ in $`L^2`$, then
    $`G=0`$. ([HS23, Definition 2.20 and Remark 2.22].)

20. **[The spectral gap inequality](../RegularityStructures/Statements/MalliavinSpectralGap.lean)**
    (`Statements.malliavin_spectral_gap`) — For a white noise on a probability space, every $`F`$ in the closure
    $`D^{1,2}`$ of the cylindrical functionals satisfies $`\mathrm{Var}\,F\le\lVert DF\rVert^2`$.

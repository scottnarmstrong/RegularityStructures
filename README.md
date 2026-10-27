# Regularity structures and the dynamical Φ⁴₃ model, formalized in Lean 4

[![Build and verify](https://github.com/scottnarmstrong/RegularityStructures/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/RegularityStructures/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/RegularityStructures/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/RegularityStructures/actions/workflows/comparator.yml)

A Lean 4 and Mathlib formalization of the convergence of the renormalised dynamical $`\Phi^4_3`$ model on the
three-dimensional torus, Theorem 1.15 of

> Martin Hairer, *A theory of regularity structures*, Inventiones mathematicae 198 (2014), 269–504
> ([DOI](https://doi.org/10.1007/s00222-014-0505-4); [arXiv:1303.5113](https://arxiv.org/abs/1303.5113v4)), cited as
> [Hai14],

together with the general theory of regularity structures that it uses, in the semigroup formulation of

> Masato Hoshino, *A semigroup approach to the reconstruction theorem and the multilevel Schauder estimate*, Annales
> Henri Lebesgue 8 (2025), 151–180 ([DOI](https://doi.org/10.5802/ahl.232);
> [arXiv:2310.07396](https://arxiv.org/abs/2310.07396v2)), cited as [Hos25],

and the global dynamics of the equation, after

> Jean-Christophe Mourrat and Hendrik Weber, *The dynamic $`\Phi^4_3`$ model comes down from infinity*, Communications in
> Mathematical Physics 356 (2017), 673–753 ([arXiv:1601.01234](https://arxiv.org/abs/1601.01234v3)), cited as [MW17], and
> Augustin Moinat and Hendrik Weber, *Space-time localisation for the dynamic $`\Phi^4_3`$ model*, Communications on Pure
> and Applied Mathematics 73 (2020), 2519–2555 ([arXiv:1811.05764](https://arxiv.org/abs/1811.05764v1)), cited as [MW20].

The equation is $`\partial_tu=\Delta u-u^3+au+\xi`$, with space-time white noise $`\xi`$ on $`\mathbb R\times\mathbb T^3`$. Its
solution is a distribution of negative regularity, whose cube is not defined; so the noise is mollified and the mass
renormalised to $`a+3C_1^\varepsilon-9C_2^\varepsilon`$, with constants diverging like $`\varepsilon^{-1}`$ and
$`\lvert\log\varepsilon\rvert`$, and the solutions converge to a limit that does not depend on the mollifier. Following
Hairer, the proof describes the solution locally by finitely many explicit stochastic objects (a model), solves a
fixed point for the coefficients, reconstructs a distribution from them, and shows that the renormalised models converge.

The library contains no `sorry`, and every main result uses only the standard Mathlib axioms.

## The main result

Let $`W`$ be a space-time white noise on $`\mathbb R\times\mathbb T^3`$, $`\mathbb T^3=\mathbb R^3/\mathbb Z^3`$, on a probability space; let
$`\rho\in C_c^\infty(\mathbb R\times\mathbb R^3)`$ be a mollifier ($`\int\rho=1`$, no symmetry assumed) and $`\xi_\varepsilon`$ the noise
mollified by $`\rho`$ at scale $`0\lt\varepsilon\le1`$, a smooth field. Let $`a\in\mathbb R`$, let $`u_0`$ be smooth on $`\mathbb T^3`$, and let
$`u_\varepsilon(\omega)`$ be the classical solution of

```math
\partial_tu_\varepsilon=\Delta u_\varepsilon-u_\varepsilon^3+\bigl(a+3C_1^\varepsilon-9C_2^\varepsilon\bigr)u_\varepsilon+\xi_\varepsilon,\qquad u_\varepsilon(0,\cdot)=u_0,
```

where $`C_1^\varepsilon`$ and $`C_2^\varepsilon`$ are two explicit Gaussian integrals built from the massive heat kernel
([Hai14, Remark 10.23]). Write $`\mathcal C^\eta`$, $`\eta\lt0`$, for the Hölder–Besov space of negative regularity, the
closure of $`C(\mathbb T^3)`$ for the heat-semigroup norm $`\lVert f\rVert_\eta=\sup_{0\lt s\le1}s^{-\eta/2}\lVert P_sf\rVert_\infty`$.

**Theorem A ([Hai14, Theorem 1.15], with smooth initial data and explicit constants).** For every
$`-2/3\lt\eta\lt-1/2`$ there are a random time $`\tau\colon\Omega\to(0,\infty]`$ and, for each $`\omega`$, a continuous path
$`u(\omega,\cdot)\colon[0,\tau(\omega))\to\mathcal C^\eta`$ such that

- (A1) $`u(\omega,0)=u_0`$, and $`\omega\mapsto u(\omega,t)`$ is measurable on $`\{\tau\gt t\}`$;
- (A2) if $`\tau(\omega)\lt\infty`$, then $`\sup_{t\lt\tau(\omega)}\lVert u(\omega,t)\rVert_\eta=\infty`$;
- (A3) for all $`T,\delta\gt0`$,
  $`\lim_{\varepsilon\downarrow0}\mathbb P\bigl(\tau\gt T\ \text{and}\ \sup_{t\le T}\lVert u_\varepsilon(t)-u(t)\rVert_\eta\gt\delta\bigr)=0`$;
- (A4) for every other mollifier $`\rho'`$, with regularised noises driven by the same $`W`$, every pair $`(\tau',u')`$ that
  satisfies (A1)–(A3) for $`\rho'`$ has $`\tau'=\tau`$ almost surely, and almost surely $`u'(t)=u(t)`$ for all $`t\lt\tau`$.

So the solutions converge in probability in $`\mathcal C^\eta`$, uniformly on compact time intervals, up to the maximal
existence time of the limit, and the limit and its maximal time do not depend on the mollifier. The self-contained note
[`docs/statement.pdf`](docs/statement.pdf) states the theorem with all its definitions. Conditions (A1)–(A3) determine the
limit (its Proposition 3.1), and the white noise, the regularised noises, finite constants and classical solutions
exist, so the theorem is not vacuous.

The library also proves the general theory in its own right: the reconstruction theorem ([Hai14, Theorem 3.10];
[Hos25, Theorem 4.1]) with its Lipschitz bound and uniqueness, and weighted reconstruction ([Hos25, Theorem 4.1]); the
multilevel Schauder estimate ([Hai14, Theorem 5.12], first part, and (5.17)); maximal solutions and the blow-up
alternative (the argument behind [Hai14, Proposition 7.11]); and, for white noise, closability of the Malliavin
derivative and the spectral gap inequality ([HS23, Definition 2.20 and Remark 2.22]). The list of main results has 23
entries; all are stated, with their exact hypotheses and links to the Lean statements, in
[docs/main-results.md](docs/main-results.md).

## Global dynamics

The limit of Theorem A never explodes, and it defines a Markov process with an invariant measure. Fix $`a\in\mathbb R`$
and $`-2/3\lt\eta\lt-1/2`$. On a complete probability space carrying a space-time white noise $`W`$, write
$`u(t,s;x)(\omega)`$ for the state at time $`t`$ of a flow started from $`x\in\mathcal C^\eta`$ at time $`s`$, and
$`\mathcal F_{s,t}`$ for the $`\sigma`$-algebra generated by the null sets and by the noise in the window $`(s,t]`$.

**Global dynamics of the $`\Phi^4_3`$ equation** (`GlobalPhi43.Statements.globalDynamics`). There is a function
$`K\colon[1,\infty)\to[0,\infty)`$, chosen before the probability space, such that on every such space there are an event
$`\Omega_0`$ of probability one, a flow $`u`$ on $`\mathcal C^\eta`$ and a probability measure $`\mu`$ on $`\mathcal C^\eta`$
with:

- (B1) $`u`$ is jointly measurable, the identity off $`\Omega_0`$, continuous in $`(t,x)`$ for $`t\ge s`$, with
  $`u(s,s;x)=x`$ and $`u(r,s;u(s,t;x))=u(r,t;x)`$ for $`t\le s\le r`$;
- (B2) $`u(t,s;x)`$ is $`\mathcal F_{s,t}`$-measurable;
- (B3) for every mollifier and smooth $`x`$, the solutions $`u_\varepsilon`$ of Theorem A started from $`x`$ converge to
  $`u(\cdot,0;x)`$ in probability in $`\mathcal C^\eta`$, uniformly on compact time intervals, and the pair
  $`(\tau\equiv\infty,u(\cdot,0;x))`$ satisfies (A1)–(A3);
- (B4) coming down from infinity ([MW17, (1.27)]): for every $`s\ge0`$ and $`p\ge1`$,
  $`\mathbb E\bigl[\sup_{x\in\mathcal C^\eta}\sup_{0\lt t\le1}(\sqrt t\,\lVert u(s+t,s;x)\rVert_\eta)^p\bigr]\le K(p)`$;
- (B5) the laws of $`(u(s+t_i,s;x_i))_i`$ and $`(u(t_i,0;x_i))_i`$ agree;
- (B6) $`P_t(x,A)=\mathbb P(u(t,0;x)\in A)`$ is a Feller Markov semigroup for the filtration $`\mathcal F_{0,t}`$;
- (B7) $`\mu P_t=\mu`$, $`\mu`$ is a weak limit of the time averages $`T^{-1}\int_0^T\mathrm{Law}(u(t,0;0))\,dt`$
  (Krylov–Bogoliubov), and $`\mu`$ has every moment of the stronger norms $`\lVert\cdot\rVert_{\eta'}`$,
  $`\eta\le\eta'\lt-1/2`$;
- (B8) started from an independent $`\mu`$-distributed field, $`u`$ is a stationary solution.

Two companion results are stated separately. The **uniform moment bound for the regularised equations**
(`GlobalPhi43.Statements.regularisedBound`) bounds the moments of
$`\sup_x\sup_{0\lt t\le1}\sqrt t\,\lVert u_\varepsilon(t)\rVert_{\eta'}`$ for the solutions of Theorem A from smooth data,
uniformly in $`\varepsilon\in(0,1]`$, by a constant chosen before the probability space; it rests on the local estimate
[MW20, Theorem 2.1], adapted to solutions with smooth defects. **Compatibility across Hölder exponents**
(`GlobalPhi43.Statements.exponentCompatibility`) chooses the flows for all exponents at once: for each pair
$`\eta\lt\eta''\lt-1/2`$ of admissible exponents, almost surely the embedding $`\mathcal C^{\eta''}\to\mathcal C^\eta`$
intertwines the two flows simultaneously for every $`0\le s\le t`$ and every datum in $`\mathcal C^{\eta''}`$ (the
event may depend on the pair).

## Results from other papers

- **[Hos25]** Theorem 4.1, reconstruction for coherent germs, unweighted and with a polynomially moderate weight, and
  the semigroup formulation, used throughout the library. Its regularity-integrability structures are not formalized.
- **[HS23]** Martin Hairer and Rhys Steele, *The BPHZ theorem for regularity structures via the spectral gap
  inequality*, Archive for Rational Mechanics and Analysis 248 (2024), article 9
  ([DOI](https://doi.org/10.1007/s00205-023-01946-w); [arXiv:2301.10081](https://arxiv.org/abs/2301.10081v3)). Adapted,
  not formalized as such: the stochastic estimates for the $`\Phi^4_3`$ models are proved directly for the
  space-periodic noise; Definition 2.20 and Remark 2.22 (closability of the Malliavin derivative) and the spectral gap
  inequality are library theorems. Their general BPHZ theorem is not formalized.
- **[BH26]** Ismaël Bailleul and Masato Hoshino, *Random models on regularity-integrability structures*
  ([arXiv:2310.10202](https://arxiv.org/abs/2310.10202v4)). Used as a methodological comparison for the convergence of
  the models; none of its theorems is formalized.
- **[MW17]** The bound (1.27), coming down from infinity, adapted to the unit torus and the constants of Theorem A, and
  the global flow, its Markov property and the invariant measure that it yields.
- **[MW20]** Theorem 2.1, the local bound, adapted to solutions with smooth defects, with Lemma 2.7, Theorem 2.8,
  Lemmas 2.9–2.10 and Corollary 2.12 as corrected in the errata. Numbering refers to the arXiv versions linked in this
  README.

## Scope

- **Theorem A.** The initial data are smooth; rough initial data in $`\mathcal C^\alpha`$ are not covered. The constants
  are Hairer's (10.33) and (10.41) with the massive heat kernel in place of his truncated kernel, which changes them by
  mollifier-independent limits. Convergence is up to the maximal existence time of the limit, instead of convergence of
  stopped processes. The torus has side one and the coupling is one.
- **The $`\Phi^4_3`$ structure.** The proof uses a finite regularity structure: the eight symbols of negative homogeneity,
  the symbols of positive homogeneity needed by the fixed point, and the abstract polynomials. General regularity
  structures of decorated trees and Hairer's wavelet analysis are not formalized; distributions are handled through
  their regularisations by the heat semigroup, as in [Hos25].
- **Reconstruction.** The structure has finitely many homogeneities and a finite-dimensional model space. The bounds on
  the model and on $`f`$ hold globally, whereas Hairer's Theorem 3.10 is local, on compact sets; so the theorem does not
  apply directly to models whose bounds hold only locally, such as random models. The bound (3.3) and the uniqueness
  statement are on $`\mathbb R^4`$ with the parabolic heat semigroup and assume that every degree below $`\gamma`$ exceeds
  $`-4`$; uniqueness is among measurable distributions with a global bound $`\lvert\Lambda_u\rvert\le C\,u^{\alpha/4}`$,
  $`0\lt u\le1`$, for some $`\alpha\gt-4`$. Hoshino's weighted and regularity-integrability conclusions are not stated.
- **Schauder estimates.** Both statements are for the parabolic heat kernel, with gain two and global bounds, and
  assume joint measurability of the model. Every degree of the structure below $`\gamma`$ must exceed $`-2`$, which excludes
  the noise symbol of the $`\Phi^4_3`$ structure. The sector must be a coordinate sector, spanned by basis vectors,
  whereas Hairer allows any sector. The integration map has no component in the abstract polynomials, and the
  non-integrality conditions can be stronger than Hairer's. The identity (5.17) also assumes a global bound on the model
  up to level $`\gamma+2`$. The local Lipschitz estimate in the model is not stated. Theorem A does not use these
  statements: its proof uses the singular Schauder estimate of [Hai14, Section 7] for the $`\Phi^4_3`$ structure.
- **Maximal solutions.** The statements are the abstract patching argument behind [Hai14, Proposition 7.11]; their
  hypotheses must be checked for each equation.
- **Global dynamics.** The state space is the whole of $`\mathcal C^\eta`$; the torus, the constants and the exponent
  range are those of Theorem A. The invariant measure is not claimed to be unique, the strong Feller property is not
  claimed, and the stationary solution is one-sided in time.
- **Differences from the printed statements** are recorded in
  [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md).

## How to verify

Install [Lean's elan toolchain manager](https://github.com/leanprover/elan). The file [`lean-toolchain`](lean-toolchain)
selects **`leanprover/lean4:v4.35.0-rc2`**, and [`lake-manifest.json`](lake-manifest.json) pins Mathlib **`v4.35.0-rc2`**
(commit **`065356127b1dc0016f66b7283ce0ce2c4055aa55`**) and all other dependencies; do not run `lake update`. From the
repository root:

```sh
lake exe cache get
lake build
python3 scripts/check-axioms.py
```

The first command downloads the compiled Mathlib. The second builds the library and the examples in
[`tests/`](tests/). The third runs `#print axioms` on each
of the 23 main results listed in [`formalization.yaml`](formalization.yaml) and checks that every one uses only the
standard Mathlib axioms, so that no proof relies on `sorry` or on an added axiom. A successful build alone does not show
this, since Lean compiles a theorem proved by `sorry` with only a warning. The [build workflow](.github/workflows/build.yml)
also runs [`check-no-sorry.py`](scripts/check-no-sorry.py) (no `sorry`, `admit` or `axiom` outside the comparator
Challenges), [`check-lean-sources.py`](scripts/check-lean-sources.py) and [`check-metadata.py`](scripts/check-metadata.py).

Reading the statements against the papers is the part of the check that a computer cannot do. Each main result has its
own short file, stating it with its definitions; [docs/main-results.md](docs/main-results.md) links to all 23.

## Single-file restatements of the main theorems

Six comparator configurations restate main results in single files that import only Mathlib and define every object
the statements use. In each, `Challenge.lean` leaves each theorem selected by `comparator.json` as an intentional `sorry` (the
supporting lemmas in the Challenge are proved there), `Solution.lean` proves the same statements from this library, and Lean's [comparator](https://github.com/leanprover/comparator), configured by
`comparator.json`, checks that Challenge and Solution state the same theorems over the same definitions and that the
Solution uses only the standard Mathlib axioms. It replays the Solution through both the Lean kernel and the
independent NanoDa kernel.

| Configuration | Theorems |
| --- | --- |
| [`comparators/TheoremA`](comparators/TheoremA/) | Theorem A, Proposition 3.1, and Lemma 4.1 (W1)–(W4) of the statement (6 theorems) |
| [`comparators/Reconstruction`](comparators/Reconstruction/) | [Hai14, Theorem 3.10] as in the library: reconstruction, the bound (3.4), the bound (3.3) for rescaled test functions and uniqueness; with four supporting statements on the parabolic heat kernel (8 theorems) |
| [`comparators/GlobalDynamics`](comparators/GlobalDynamics/) | The global dynamics of the $`\Phi^4_3`$ equation, (B1)–(B8); with the theorems of Theorem A's Challenge showing that its objects exist and the characterisation of the extended norm (7 theorems) |
| [`comparators/RegularisedBound`](comparators/RegularisedBound/) | The uniform moment bound for the regularised equations; with the same four theorems on its hypotheses (5 theorems) |
| [`comparators/ExponentCompatibility`](comparators/ExponentCompatibility/) | Compatibility of the global flows across Hölder exponents; with the same four theorems and the characterisations of the extended norm and of the embeddings (9 theorems) |
| [`comparators/Schauder`](comparators/Schauder/) | [Hai14, Theorem 5.12], first part, and (5.17), as in the library; with the convergence of the series defining the operator, the existence of the annihilating bump function, and four supporting statements on the parabolic heat kernel (8 theorems) |

To run them as the [Palomar registry](https://submit.palomar-registry.org/) does, install
[bubblewrap](https://github.com/containers/bubblewrap) and run `scripts/verify-comparator.sh`, as the
[comparator workflow](.github/workflows/comparator.yml) does; it first runs
[`check-comparator-layout.py`](scripts/check-comparator-layout.py), which rejects a module layout the registry refuses.
When reading the Challenges, keep in mind:

- The TheoremA Challenge includes the theorems showing that its hypotheses can be met (white noise, regularised noise,
  classical solutions), and `constants_finite` shows that every integral defining $`C_1^\varepsilon`$ and $`C_2^\varepsilon`$
  converges absolutely, so the constants are not junk values of Lean's totalised integral. $`\mathbb T^3`$ is Mathlib's
  `UnitAddTorus (Fin 3)`, and derivatives are taken on spatially periodic lifts.
- The Reconstruction and Schauder Challenges state the specialisations described under Scope, with the model bounds as
  hypotheses rather than part of the notion of model and existential constants. They represent distributions through
  the parabolic heat semigroup of order four, whose kernel properties are compared as theorems in their own right.
- The GlobalDynamics and ExponentCompatibility Challenges define $`\mathcal C^\eta`$ as in the TheoremA Challenge. The
  heat semigroup on $`\mathcal C^\eta`$ and the embeddings $`\mathcal C^{\eta''}\to\mathcal C^\eta`$ are defined as
  extensions from $`C(\mathbb T^3)`$, and companion theorems show that they are the continuous extensions, so they are
  not junk values of `UniformSpace.Completion.extension`. In ExponentCompatibility the constant profiles are existential
  and chosen before the probability space; they need not be those of GlobalDynamics.
- In the Schauder Challenge the singular part $`K`$ of the heat kernel is built with a bump function chosen with
  `Classical.choose` among the functions with the properties stated in `exists_annBump`; any such choice changes $`K`$
  only by a smooth compactly supported function.

## Errata and deviations

[docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md) records 13 errata and 18 deviations, with locations,
corrections and the effect on the stated theorems. By source: [Hai14] 1 erratum and 6 deviations, [Hos25] 0 errata
and 1 deviation, [HS23] 0 errata and 4 deviations, [BH26] 1 erratum and 3 deviations, [MW20] 10 errata and 2
deviations, [MW17] 1 erratum and 2 deviations. The errata: [Hai14, Proposition
6.12] needs the hypothesis $`\eta\le\gamma`$ (a counterexample is given, and the Lean statement carries the hypothesis);
[BH26, Sections 4.6–4.7] use a convergence of mollifications, uniform over the unit ball of the noise space, that fails
for $`L^2`$ (no conclusion of the paper is shown to be false). The [MW20] errata correct constants, radii, exponents and
the uniformity claimed in Lemma 2.11 (2.36) and Corollary 2.12 (2.38), each with a counterexample to the printed form;
none is a counterexample to [MW20, Theorem 2.1]. None of them affects the main theorems.

## Documentation

- [The 23 main results](docs/main-results.md): each result, with its hypotheses and a link to its Lean statement.
- [The statement](docs/statement.pdf) (source [`statement.tex`](docs/statement.tex)): Theorem A with all its definitions;
  the Lean documentation follows its numbering.
- [Errata and deviations](docs/ERRATA-AND-DEVIATIONS.md): errors found in the sources, and differences between the
  printed and the formalized statements.
- [Proof route and library map](docs/library.md): how the proof is organised, and where each part of it lives.
- Exact statements: [`Phi43Statements/`](Phi43Statements/), [`RegularityStructures/Statements/`](RegularityStructures/Statements/),
  [`GlobalPhi43Statements/`](GlobalPhi43Statements/).

## How this formalization was made

The proofs were written with AI coding agents under the supervision of Scott Armstrong. The author approved every
exact Lean definition and theorem statement before its proof was developed, and each statement was compared with the
sources by an independent review. The Lean kernel checks every proof. The models and tools are listed in
[`formalization.yaml`](formalization.yaml).

## Author, citation and license

The Lean development is by **Scott Armstrong**, CNRS and Laboratoire Jacques-Louis Lions, Sorbonne Université; Courant
Institute School of Mathematics, Computing, and Data Science, New York University. Scott Armstrong was supported by the
European Research Council (ERC) under the European Union's Horizon Europe research and innovation programme, grant
agreement No. 101200828.

To cite this formalization, use [`CITATION.cff`](CITATION.cff). The Lean code is licensed under the Apache License 2.0;
see [`LICENSE`](LICENSE). The license does not cover the cited papers.

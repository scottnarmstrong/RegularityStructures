# Proof route and library map

This page describes how the proofs of Theorem A and of the global dynamics are organised and where each part of the
formalization lives. The main results themselves are listed in [main-results.md](main-results.md); [Hai14], [Hos25],
[HS23], [BH26], [MW17] and [MW20] are cited as in the [README](../README.md).

## What is formalized from [Hai14]

- Theorem 1.15, as Theorem A: smooth initial data, the explicit constants $`C_1^\varepsilon`$, $`C_2^\varepsilon`$, and
  convergence up to the maximal existence time of the limit instead of convergence of stopped processes.
- Theorem 3.10 (reconstruction, the bounds (3.3) and (3.4), uniqueness) and Theorem 5.12 (the first part and (5.17)),
  for finite regularity structures, in the semigroup formulation and with global bounds; see
  [the main results](main-results.md) for the exact hypotheses.
- For the finite $`\Phi^4_3`$ structure: the fixed point for singular modelled distributions (Section 7), the canonical
  and renormalised models (Proposition 8.27, Section 9.2), the identification of the renormalised equation
  (Proposition 9.10), and the convergence of the BPHZ models (Theorem 10.22) with Hairer's constants (10.33) and
  (10.41).
- Not covered: rough initial data in $`\mathcal C^\alpha`$; general regularity structures of decorated trees; the
  wavelet analysis; the local Lipschitz estimate in the model of Theorem 5.12.
- One erratum is corrected; see [Errata and deviations](ERRATA-AND-DEVIATIONS.md).

## Proof route

The proof follows the structure of [Hai14] for $`\Phi^4_3`$, in a finite regularity structure: the eight symbols of negative
homogeneity, the symbols of positive homogeneity needed by the fixed point, and the abstract polynomials, with a
parameter $`\kappa`$ outside a finite exceptional set. Distributions are handled through their regularisations by the heat
semigroup, as in [Hos25], instead of Hairer's wavelets, and reconstruction, products and the singular Schauder estimate
are proved in that form.

The deterministic part solves the abstract fixed point for weighted singular modelled distributions on short time slabs
([Hai14, Theorem 7.8]); patching the local solutions gives the maximal solution and the blow-up alternative. On a short
window after any restart time, the distance of two solutions is controlled by the distance of their data and of their
models. For a smooth noise the renormalised canonical model is constructed and shown unique ([Hai14, Proposition 8.27]), and the reconstruction of the
fixed point is identified with the classical solution of the renormalised equation ([Hai14, Proposition 9.10]).

The stochastic part proves that the BPHZ models, renormalised with Hairer's constants for his truncated kernel, form a
Cauchy family in $`L^p`$ as $`\varepsilon\downarrow0`$, also across two mollifiers. The second moments of every tree are computed
with a Gaussian diagram formula for Wick products and the kernel estimates of [Hai14, Section 10.5]; all moments follow by
the equivalence of moments in a finite Wiener chaos; and the model norms are controlled by a Kolmogorov criterion
(an analogue of [Hai14, Theorem 10.7]). These estimates are proved directly for the space-periodic noise, rather than
taken from the general theorems of [HS23] or [BH26]. The constants of the statement differ from Hairer's by
mollifier-independent limits, so the models renormalised with them converge as well.

Convergence of the models and continuity of the solution map, restarted from data in $`\mathcal C^\eta`$, give convergence of
$`u_\varepsilon`$ up to the maximal existence time of the limit; Proposition 3.1 of the statement and the mollifier
independence of the limiting model give (A4).

**Intermediate steps.** The main steps of the proof are stated in [`Phi43Statements/Steps/`](../Phi43Statements/Steps/):
the renormalised canonical model of a smooth noise and its uniqueness
([`renormalisedCanonicalModel_existsUnique`](../Phi43Statements/Steps/RenormalisedCanonicalModel.lean), after
[Hai14, Proposition 8.27]), the Kolmogorov criterion for model norms
([`kolmogorov_modelNorm`](../Phi43Statements/Steps/KolmogorovModelNorm.lean)), the convergence of the BPHZ models
([`bphzModels_cauchy`](../Phi43Statements/Steps/BphzModelsCauchy.lean), after [Hai14, Theorem 10.22]) and of the models
renormalised with the constants of Theorem A ([`phi43GModels_convergence`](../Phi43Statements/Steps/GModelsConvergence.lean)), the
convergence of the noise potentials ([`phi43Noise_cauchy`](../Phi43Statements/Steps/NoiseCauchy.lean)), the comparison of the
constants, the equivalence of norms, and the stopped continuity of the solution map
([`phi43ClassicalSolution_stoppedContinuity`](../Phi43Statements/Steps/ClassicalSolutionStoppedContinuity.lean)).

## The global dynamics

The global theory uses the local theory of Theorem A as proved, through its statements in `Phi43Statements`.

1. **The local estimate.** [MW20, Theorem 2.1], adapted to solutions with smooth defects
   (`GlobalPhi43.mw20DefectBound`), is proved from the MW20 setting (`GlobalPhi43/MW20/Setting`): the test kernels,
   the parabolic cylinders and seminorms, Lemma 2.7, Theorem 2.8, Lemmas 2.9–2.10 and Corollary 2.12, with the
   corrections recorded in the errata.
2. **Attachment to Theorem A.** The solutions of Theorem A are written in the form of the local estimate, with the
   trees of the canonical model and smooth defects; the bound on the model on compact sets
   (`GlobalPhi43.modelTestBound`) and the time translation of the model (`GlobalPhi43.translationInterface`) give the
   moments. This proves the uniform moment bound for the regularised equations.
3. **The global flow.** The moment bound excludes explosion, so the limits of Theorem A exist for all times and all
   starts; they are extended from smooth to all data in $`\mathcal C^\eta`$ by continuity, on one event of probability
   one, which gives (B1)–(B3) and (B5). Coming down from infinity (B4) follows from the moment bound by Fatou's lemma
   over a countable dense set of data and the continuity in (B1).
4. **Markov process and invariant measure.** Adaptedness and time homogeneity give the Markov and Feller properties
   (B6). The sublevel sets of the stronger norms are relatively compact in $`\mathcal C^\eta`$
   (`GlobalPhi43.compactSublevel`), so the time averages of the laws are tight, and the Krylov–Bogoliubov procedure gives
   the invariant measure (B7) and the stationary solution (B8).
5. **Compatibility across exponents.** For each exponent the flow is built from the same approximants; the embedding
   $`\mathcal C^{\eta''}\to\mathcal C^\eta`$ commutes with their limits, and density extends the identity to all data.

## Library map

Each main result has its own short file, stating it with its definitions; its proof is in the topic directories below.
The repository has about 2,200 Lean files and 290,000 lines, all in Lean's module system and none longer than 1,500
lines.

| Directory | Content |
| --- | --- |
| [`Phi43Statements`](../Phi43Statements/) | Theorem A, Proposition 3.1 and Lemma 4.1 of the statement, one per file; [`Defs`](../Phi43Statements/Defs/) and [`Steps`](../Phi43Statements/Steps/), the intermediate steps |
| [`RegularityStructures/Statements`](../RegularityStructures/Statements/) | The theorems of the general theory, one per file |
| [`RegularityStructures/Abstract`](../RegularityStructures/Abstract/) | Regularity structures, models, modelled distributions, reconstruction, products, abstract integration and the multilevel Schauder estimate, singular modelled distributions, the fixed point and maximal solutions |
| [`RegularityStructures/Analysis`](../RegularityStructures/Analysis/) | Regularising semigroups, the parabolic heat semigroup and its kernels, parabolic geometry |
| [`RegularityStructures/Torus`](../RegularityStructures/Torus/) | The torus, periodic heat kernels, the norm of $`\mathcal C^\eta`$ and its equivalence with the Littlewood–Paley norm |
| [`RegularityStructures/Probability`](../RegularityStructures/Probability/), [`RegularityStructures/BPHZ`](../RegularityStructures/BPHZ/) | Gaussian vectors, white noise, the Isserlis formula, Gaussian Poincaré and spectral gap inequalities, Malliavin calculus, Kolmogorov criteria, convergence in probability and moments in finite chaos |
| [`RegularityStructures/PDE`](../RegularityStructures/PDE/) | The heat equation on the torus, Duhamel's formula, mild and classical solutions, the maximum principle |
| [`Phi43/Structure`](../Phi43/Structure/) | The finite $`\Phi^4_3`$ regularity structure, its structure group, renormalisation and canonical models |
| [`Phi43/BPHZ`](../Phi43/BPHZ/), [`Phi43/Stochastic`](../Phi43/Stochastic/), [`Phi43/RegularisedNoise`](../Phi43/RegularisedNoise/) | The BPHZ models and their moments, the constants and their comparison, the regularised noise |
| [`Phi43/FixedPointF`](../Phi43/FixedPointF/), [`Potential`](../Phi43/Potential/), [`Inhomogeneity`](../Phi43/Inhomogeneity/), [`Restart`](../Phi43/Restart/), [`Persistence`](../Phi43/Persistence/), [`LocalLipschitz`](../Phi43/LocalLipschitz/), [`Reconstruction`](../Phi43/Reconstruction/), [`Identification`](../Phi43/Identification/) | The deterministic solution map: the fixed point, potentials, restarts, local Lipschitz dependence, and the identification with classical solutions |
| [`Phi43/ClassicalSolution`](../Phi43/ClassicalSolution/), [`Phi43/Torus`](../Phi43/Torus/) | Classical solutions and kernel bounds on the torus |
| [`Phi43/TheoremA`](../Phi43/TheoremA/) | The assembly of Theorem A |
| [`GlobalPhi43Statements`](../GlobalPhi43Statements/) | The global dynamics, the uniform moment bound for the regularised equations and the compatibility across Hölder exponents, one per file; [`Defs`](../GlobalPhi43Statements/Defs/), the clauses (B1)–(B8) and the objects they use |
| [`GlobalPhi43/MW20`](../GlobalPhi43/MW20/) | The MW20 setting ([`Setting`](../GlobalPhi43/MW20/Setting/)) and the local estimate with smooth defects |
| [`GlobalPhi43/Local`](../GlobalPhi43/Local/), [`GlobalPhi43/Attachment`](../GlobalPhi43/Attachment/) | The local Schauder and maximum-principle arguments, and the attachment of the local estimate to the solutions of Theorem A |
| [`GlobalPhi43/Flow`](../GlobalPhi43/Flow/), [`GlobalPhi43/Assembly`](../GlobalPhi43/Assembly/) | The global flow from all data and all starts, coming down from infinity and the moments of the stronger norms |
| [`GlobalPhi43/Markov`](../GlobalPhi43/Markov/), [`GlobalPhi43/Invariant`](../GlobalPhi43/Invariant/), [`GlobalPhi43/Compactness`](../GlobalPhi43/Compactness/), [`GlobalPhi43/Probability`](../GlobalPhi43/Probability/) | The Markov and Feller properties, compact sublevel sets, the Krylov–Bogoliubov invariant measure and the stationary solution |
| [`GlobalPhi43/Compatibility`](../GlobalPhi43/Compatibility/), [`GlobalPhi43/Proofs`](../GlobalPhi43/Proofs/) | Compatibility across exponents, and the proofs of the statements in `GlobalPhi43Statements` |
| [`tests`](../tests/) | Examples: [`Witnesses`](../tests/Witnesses/), showing that the hypotheses of the statements are jointly satisfiable, and [`regression`](../tests/regression/), showing that the definitions exclude degenerate objects |
| [`comparators`](../comparators/) | The six Mathlib-only comparator configurations |

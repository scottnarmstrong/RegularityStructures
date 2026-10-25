# Errata and deviations

This document separates printed errors from deliberate choices made by the formalisation. An erratum is a defect in the cited source itself: a missing hypothesis, an incorrect conclusion, or a proof step that does not follow from the printed assumptions. A deviation records a change of scope, convention, topology, interpretation, or proof strategy. Locations below refer to the arXiv versions listed in the source table; theorem and equation numbers are those versions' numbers.

The main source is Hairer, *A theory of regularity structures*, pinned as arXiv:1303.5113v4. The analytic supplement is Hoshino, pinned as arXiv:2310.07396v2. The stochastic sources are Hairer–Steele, pinned as arXiv:2301.10081v3, and Bailleul–Hoshino, pinned as arXiv:2310.10202v4. LOTT24 and BHZ19 are used as methodological and algebraic references; their pinned citations, together with the remaining reference-only sources, are recorded below.

| Source | Errata | Deviations |
|---|---:|---:|
| Hai14 | 1 | 6 |
| Hos25 | 0 | 1 |
| HS23 | 0 | 4 |
| BH26 | 1 | 3 |
| LOTT24 | 0 | 0 |
| BHZ19 | 0 | 0 |
| **Total** | **2** | **14** |

The table counts entries in the source sections below. The final proof-strategy section is explanatory and is not counted separately.

## Hai14: Hairer 2014

### Errata

1. **pp. 91–92, Proposition 6.12 and its proof, (6.10)–(6.12).** Missing hypothesis. Definition 6.2 allows any `η ∈ ℝ`, and Propositions 6.9, 6.13 and 6.16 assume `η ≤ γ` or `η < γ` explicitly. Proposition 6.12 sets `η = (η₁ + α₂) ∧ (η₂ + α₁) ∧ (η₁ + η₂)` but does not assume `η ≤ γ`, and without it the conclusion `f₁ ⋆_γ f₂ ∈ D_P^{γ,η}` can fail. Take the polynomial structure on `ℝ` truncated at degree one (`T = ⟨1, X⟩`, `X ⋆ X = 0`), `P = {0}`, `γ₁ = γ₂ = γ ∈ (1, 2)`, `α₁ = α₂ = 0`, `η₁ = η₂ = 3`, and `f₁ = f₂ = φ 1 + φ′ X` with `φ` smooth and bounded and `φ(x) = x` near `0`. The increments of `fᵢ` vanish near `P`, so `fᵢ ∈ D_P^{γ,3}`, and the printed exponent is `η = 3 > γ`. The `X`-component of the increment of `f₁ ⋆_γ f₂ = φ² 1 + 2φφ′ X` between `x = λ` and `y = 2λ` is `2λ`, while `D_P^{γ,3}` requires it to be `O(λ^{γ−1} λ^{3−γ}) = O(λ²)`. In the proof, the term of (6.12) with `m ≤ η₁` and `n ≤ η₂` has exponent `m + n − γ`, which need not dominate `η − γ`. The correction is to add `η ≤ γ`, or equivalently to conclude `f₁ ⋆_γ f₂ ∈ D_P^{γ, η ∧ γ}`. The hypothesis holds automatically when `ηᵢ ≤ γᵢ`, and Hairer's Φ⁴₃ application, Lemma 9.7, satisfies it. The corrected statement, with the hypothesis `η ≤ γ`, is `Model.singularBoundOn_truncMul_near` in [`WeightedSingularProductNear.lean`](../RegularityStructures/Abstract/WeightedSingularProductNear.lean). The counterexample is explained in the module documentation of [`WeightedSingularProduct.lean`](../RegularityStructures/Abstract/WeightedSingularProduct.lean); it is not a Lean theorem. Effect on the stated theorems: none; the formal statement carries the hypothesis `η ≤ γ`, and every use satisfies it.

### Deviations

1. **Theorem 1.15 and Remarks 1.13, 1.16–1.18.** Hairer states rough initial data in `C^α` and convergence through stopped processes. The formalised headline fixes smooth initial data, keeps Hairer’s exponent interval `(-2/3, -1/2)`, and assembles a path up to its maximal existence time in the completed negative Hölder space. This is a deliberately narrower and differently packaged headline; it does not claim the full rough-data statement from Theorem 1.15. Effect on the stated theorems: The formalised theorem has the stated smooth-data scope rather than Hairer’s full rough-data scope.

2. **Theorem 1.15, Theorem 10.22, and constants (10.33) and (10.41).** Hairer allows suitably chosen counterterms and uses the truncated heat kernel in the model construction. The formalisation names the two Gaussian constants built from the massive heat kernel, fixes the torus and coupling conventions, and incorporates the mass parameter as a fixed linear shift. The comparison with Hairer’s compactly supported kernel is therefore an additional identification step. Effect on the stated theorems: The formalised theorem asserts convergence for the displayed explicit constants; this is stronger and more specific than the literal “suitably chosen constants” wording.

3. **Propositions 9.8 and 9.10, and Theorem 10.22.** Hairer’s proof uses the regularity-structures fixed-point theorem, wavelet/model estimates, and the model convergence theorem in Section 10.5. The formalisation exposes the semigroup reconstruction and Schauder estimates, the finite Φ⁴₃ sector, the explicit renormalised equation, and the stochastic convergence interface as separate mathematical components. Hairer’s results remain the source of the comparison statements, not a claim that the formalisation has reproduced every intermediate construction verbatim. Effect on the stated theorems: No effect on the stated theorems; this is a proof-interface and exposition choice.

4. **Theorem 5.12 (the library statements `Statements.Model.kGamma_mem_modelledDistributions` and `Statements.Model.reconstruct_kGamma`).** Every degree of the regularity structure below `γ` must exceed `−2`, not only the degrees occurring in the sector `V`. This excludes the noise symbol `Ξ` of the Φ⁴₃ structure, of degree `−5/2 − κ`, so these statements do not apply to the Φ⁴₃ structure itself. The integration map has no component in the abstract polynomials, and only the first half of the theorem is stated: the bound `𝒦_γ : D^γ → D^{γ+2}` and (5.17), not the local Lipschitz estimate in the model. A non-degenerate example of the hypotheses is `SchauderWitness.schauderSetting_witness` in [`SchauderSetting.lean`](../tests/Witnesses/SchauderSetting.lean). Effect on the stated theorems: none on Theorem A, which uses the singular Schauder estimate of Section 7 instead.

5. **Theorems 3.10 and 5.12 (the library statements `Statements.Model.exists_reconstruction`, `Statements.Model.abs_reconstruct_sub_reconstruct_le`, `Statements.Model.abs_pairing_rescaledTestFunction_le`, `Statements.Model.eq_reconstruct_of_abs_pairing_le`, `Statements.Model.kGamma_mem_modelledDistributions` and `Statements.Model.reconstruct_kGamma`).** Hairer's bounds are local: the model and the modelled distribution are bounded on compact sets, and so is the conclusion. The library statements assume global bounds (on all of space-time) for the model and for `f`. They therefore do not apply directly to models whose bounds hold only locally, such as the random BPHZ models. Effect on the stated theorems: none on Theorem A; the restriction concerns these library statements only.

6. **Proposition 7.11 (the library statements `Statements.exists_maximal_solution` and `Statements.exists_global_solution_of_bound`).** These are the abstract patching argument behind Proposition 7.11 and the discussion after it, for an arbitrary solution relation with local existence, local uniqueness, restriction and an autonomous gluing hypothesis. They are not Proposition 7.11 itself, which concerns the solutions of the fixed point of Section 7; the hypotheses must be verified for each equation. Effect on the stated theorems: none on Theorem A, whose maximal solution is assembled separately.

## Hos25: Hoshino 2025

### Errata

No source erratum is retained for the pinned text.

### Deviations

1. **Theorem 4.1 and Theorem 5.12.** Hoshino proves semigroup reconstruction and multilevel Schauder estimates in a weighted regularity-integrability setting on the general spaces of the paper. The formalisation uses the semigroup mechanism in the finite Φ⁴₃ sector and its periodic setting, with the weights and model bounds specialised to the theorem at hand. It does not present the whole regularity-integrability framework as a formalised theorem. The library statements of reconstruction and of the Schauder estimate (`RegularityStructures/Statements/`) are specialised in the same way, and also relative to Hairer's Theorems 3.10 and 5.12: a regularity structure has a finite graded basis (a finite-dimensional model space, finitely many homogeneities); reconstruction assumes `γ > 0` and global bounds on the model and on `f`, and its test-function bound and uniqueness statement on `ℝ⁴` assume that every degree below `γ` exceeds `−4`, and uniqueness is among measurable distributions `Λ` with a global bound `|Λ_u| ≤ C u^{α/4}`, `0 < u ≤ 1`, for some `α > −4`; the Schauder statements are for the parabolic heat kernel with gain two, require every degree below `γ` to exceed `−2` (which excludes the Φ⁴₃ noise symbol), require the sector `V` to be a coordinate sector (whenever `a ∈ V` has a nonzero coordinate `j`, the basis vector `e_j` lies in `V`; Hairer's Definition 2.5 allows any graded invariant subspace with homogeneous complements), have an integration map with no polynomial component and non-integrality conditions that can be stronger than `γ + β ∉ ℕ`, assume joint measurability of the model, and state only the first part of Theorem 5.12; the identity (5.17) also assumes a global bound on the model up to level `γ + 2`. Effect on the stated theorems: none on Theorem A, whose proof uses the singular Schauder estimate of Hairer's Section 7; the library statements carry these restrictions as hypotheses.

## HS23: Hairer–Steele 2023

### Errata

No source erratum is retained for the pinned text.

### Deviations

1. **Theorem 2.33 and Remark 2.34.** The theorem gives convergence in probability along the paper’s approximation sequence, while the mollifier-independence argument is stated in a remark through an alternating sequence. The formalisation needs a continuous-parameter, cross-mollifier Cauchy statement with moment bounds, so it supplies that interface explicitly rather than reading an `L^p` rate or a continuous-parameter theorem into Theorem 2.33. Effect on the stated theorems: The formalised stochastic input has stronger quantifiers than the cited theorem and is not attributed to HS23 alone.

2. **Theorem 2.33 and the spectral-gap setup of Sections 2 and 6.** HS23 works on the whole space. The formalisation works with space-periodic noise on `R × T³` and does not use HS23’s whole-space spectral-gap and localisation steps; it proves the needed Gaussian moment bounds directly for the periodic noise (see item 3 of the proof-strategy section). Effect on the stated theorems: The formalised theorem is periodic; HS23 is not cited as already proving that periodic adaptation.

3. **Theorem 2.33 and the finite Φ⁴₃ sector.** HS23 treats a general reduced regularity structure and its BPHZ model. The formalisation identifies the relevant BPHZ characters with the two explicit Φ⁴₃ constants and works in the finite sector needed for the renormalised cubic equation. Effect on the stated theorems: No effect on the stated theorems; this records the narrower algebraic interface actually used.

4. **Lemma 6.4 and the mollifier class.** HS23 does not define the word *mollifier*. The proof of Lemma 6.4 (p. 67) treats `̺ⁿ(z) dz` as a probability measure: it bounds `|ψ^λ − ̺^{n₁} ∗ ψ^λ|` by `∫ |ψ^λ(y) − ψ^λ(y − z)| ̺^{n₁}(z) dz`, and for `λ < 2^{−n₁}` it applies Jensen's inequality. Both steps are valid for nonnegative mollifiers. The formalisation's mollifiers are smooth, compactly supported and of integral one, with no sign condition. It therefore replaces `̺ⁿ` by `|̺ⁿ|` and Jensen's inequality by the Cauchy–Schwarz inequality, at the cost of a factor `‖̺‖_{L¹}`, and carries such `L¹` bounds through the convolution estimates. It also treats every scale `ε ∈ (0, 1]` rather than only the dyadic sequence used in the source. Effect on the stated theorems: none; this is a proof supplement and does not change the smooth-noise equation or its explicit counterterms.

## BH26: Bailleul–Hoshino 2026

### Errata

1. **pp. 29–30, Section 4.6, step §0, and Section 4.7, (4.13).** Gap. Step §0 of the proof of the Cauchy property (4.12) states that `lim_{m,n→∞} ‖h_n − h_m‖_H = 0`, with `h_n = ϱ_n ∗ h`, holds uniformly over `‖h‖_H ≤ 1`. Section 4.7 deduces that the limit does not depend on the approximation of the identity from (4.13), under the condition `lim_{n→∞} sup_{‖h‖_H ≤ 1} ‖h ∗ ϱ_n − h ∗ ϱ̃_n‖_H = 0`. Theorem 19 allows `H = L²(ℝ^d)` for white noise. On `L²` the operator `h ↦ h ∗ k` has norm `sup_ζ |k̂(ζ)|`. For rescalings `ϱ_n = 2^{n|s|} ϱ(2^{n s} ·)`, the norm of `h ↦ h ∗ (ϱ_n − ϱ_{n+1})` is therefore a positive constant independent of `n`. For two kernel shapes at the same scale, the norm of `h ↦ h ∗ (ϱ_n − ϱ̃_n)` equals `sup_ζ |ϱ̂(ζ) − ϱ̃̂(ζ)| > 0` for every `n`. So neither uniform statement holds in the `H` norm, and the same computation applies to every space `H^{−s₀,Q}(w₀)` allowed by Theorem 19. The proof uses `h_n` only through the model norm on the noise-direction symbol. Section 4.2 bounds that norm by `‖h_n‖_{B^{r₀−ε+|s|/p}_{p,∞}(w₀)}`, and since `r₀ < −|s|/2 − s₀`, `H` embeds into this space with a strict loss of regularity. Both uniform convergences hold in that weaker norm, and using it there appears to address the gap. Effect on the stated theorems: none; no conclusion of BH26 is shown to be false, and the formalisation does not use this argument.

### Deviations

1. **Theorem 19 and Sections 2–4.** BH26 uses weighted whole-space model spaces and a regularity-integrability topology. The formalisation uses Hairer’s model topology on a finite periodic sector, with models built from a causal heat kernel. Effect on the stated theorems: No effect on the stated theorems; BH26 is a methodological comparison, not the source of the formalised topology.

2. **Section 6.2, periodic examples.** The periodic Fourier examples in BH26 are not taken as a proof that the periodic white-noise law satisfies every whole-space hypothesis of Theorem 19. The formalisation proves the periodic spectral-gap and model estimates in its own setting. Effect on the stated theorems: No effect on the stated theorems; the periodic theorem is not inferred from the example alone.

3. **Theorem 19 and Corollary 20.** BH26 permits a broad class of preparation maps and renormalisation procedures. The formalisation uses the finite Φ⁴₃ renormalisation procedure and the explicit two-constant identification needed for the equation in the headline theorem. Effect on the stated theorems: No effect on the stated theorems; the formalised result is a specialised application rather than a formalisation of BH26’s full generality.

## Reference-only pinned sources

No source-specific erratum or deviation is retained here for the following citations. They provide background, cross-checks, or context for extensions; the formalisation does not claim to reproduce their full theorems.

| Key | Pinned citation |
|---|---|
| CZ20 | arXiv:2005.09287v3 |
| BCZ24 | arXiv:2301.07517v2 |
| LOTT24 | arXiv:2112.10739v3 |
| BOT25 | arXiv:2401.05935v3 |
| Tem25 | arXiv:2303.18192v2 |
| BHZ19 | arXiv:1610.08468v4 |
| CH16 | arXiv:1612.08138v5 |
| BCCH21 | arXiv:1711.10239v4 |
| BH-tour | arXiv:2006.03524v3 |
| Hai-intro | arXiv:1401.3014v2 |
| CC18 | arXiv:1310.6869v3 |
| Kup16 | arXiv:1410.3094v2 |
| MW17 | arXiv:1601.01234v3 |
| MW20 | arXiv:1811.05764v1 |
| CMW23 | arXiv:1910.13854v2 |
| CG25 | arXiv:2510.20716v2 |
| GH21 | arXiv:1810.01700v4 |
| HSi25 | arXiv:2510.19339v1 |
| BOS25 | arXiv:2503.01621v1 |
| Duc25 | arXiv:2109.11380v3 |
| Duc26 | arXiv:2511.07120v2 |

## Deviations of proof strategy from Hairer 2014

The formalisation’s proof strategy differs from Hairer’s beyond the individual statement changes above:

1. It makes semigroup reconstruction and the multilevel Schauder estimate explicit, instead of taking Hairer’s wavelet-based analytic estimates as the visible interface.
2. It constructs and checks only the finite Φ⁴₃ sector needed for the cubic equation, including the polynomial sector, the structure-group action, and the two-constant renormalisation map. The polynomial symbols are treated separately from the non-polynomial homogeneities, as required by Hairer’s Assumption 5.3. The distinction is illustrated by [`NonIntegralityPolynomial.lean`](../tests/regression/NonIntegralityPolynomial.lean) and [`Phi4HypsInconsistent.lean`](../tests/regression/Phi4HypsInconsistent.lean).
3. It uses Gaussian Poincaré and spectral-gap estimates for the concrete periodic noise and proves the needed cross-mollifier bounds in the finite sector, rather than importing the general whole-space model-convergence theorem as a black box.
4. It identifies the smooth-noise model with the classical mild and PDE solutions, then assembles the limit through its maximal existence time. Measurability of the white-noise family and non-emptiness of the mollifier class are made explicit; the related checks are recorded in [`FakeWhiteNoise.lean`](../tests/regression/FakeWhiteNoise.lean) and [`MollifierExists.lean`](../tests/regression/MollifierExists.lean).
5. It uses a periodic adaptation of the stochastic estimates and the massive heat kernel used to define the explicit constants. The Hairer comparison kernel remains the reference object for the local singularity and counterterm identification.

These choices explain why a source theorem can be the mathematical origin of a component without being a literal description of the formalised proof route. They also delimit the claims: the document records the source correction and the formalisation’s chosen interfaces, not a blanket transfer of every hypothesis or conclusion across the cited papers.
